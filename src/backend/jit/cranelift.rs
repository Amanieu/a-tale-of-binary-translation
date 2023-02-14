use std::mem;

use cranelift::codegen;
use cranelift::codegen::ir::Endianness;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Module};
use cranelift_module::{DataId, Linkage};
use memoffset::offset_of;
use rustc_hash::FxHashMap;

use crate::frontend::{translate_one_instruction, Cond, Signed, Trans, Width};
use crate::{read_bytes, MEM_SIZE};
use crate::{Args, EmulatorState};

use super::JitFunction;

/// Type responsible for holding the backing memory of compiled JIT functions.
pub(super) struct CraneliftJitCache {
    /// The Cranelift `JITModule` which holds all of the generated code.
    module: JITModule,

    /// Referebces to JUMP_CACHE_* variables in the `JITModule`.
    jump_caches: FxHashMap<u32, DataId>,
    /// Temporary state used while compiling a function. This is kept around
    /// across multiple compilations so that the allocations are reused.
    codegen_ctx: codegen::Context,

    /// Temporary state used by `FunctionBuilder`, which is a helper type for
    /// constructing a Cranelift function.
    builder_ctx: FunctionBuilderContext,

    /// Temporary state used while compiling data objects.
    data_ctx: DataContext,
}

impl CraneliftJitCache {
    pub(super) fn new() -> Self {
        // Create an ISA with custom flags. In the next cranelift release this
        // can be simplified using JITBuilder::with_flags.
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        flag_builder.set("opt_level", "speed").unwrap();
        flag_builder.set("unwind_info", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();

        let module = JITModule::new(JITBuilder::with_isa(
            isa,
            cranelift_module::default_libcall_names(),
        ));
        let codegen_ctx = module.make_context();
        let builder_ctx = FunctionBuilderContext::new();
        let data_ctx = DataContext::new();
        Self {
            module,
            jump_caches: FxHashMap::default(),
            codegen_ctx,
            builder_ctx,
            data_ctx,
        }
    }

    pub(super) fn compile(&mut self, pc: u32, mem: &[u8; MEM_SIZE], args: &Args) -> JitFunction {
        // Define the signature of the function,
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        sig.returns
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        self.codegen_ctx.func.signature = sig;

        // Enable disassembly if dumping the genrateed code.
        self.codegen_ctx.set_disasm(args.dump_jit_code);

        // Translate and compile the main function for this block of code.
        let new_jump_targets = CraneliftTranslator::translate(
            pc,
            mem,
            args,
            &mut self.module,
            &mut self.builder_ctx,
            &mut self.codegen_ctx,
            &mut self.jump_caches,
        );
        let func = self
            .module
            .declare_function(
                &format!("block_{pc:x}"),
                Linkage::Export,
                &self.codegen_ctx.func.signature,
            )
            .unwrap();
        self.module
            .define_function(func, &mut self.codegen_ctx)
            .unwrap();

        // Dump the generated code for debugging.
        if args.dump_jit_code {
            eprintln!("Optimized cranelift IR for block at pc={pc:#x}:");
            eprintln!("================");
            eprintln!("{}", self.codegen_ctx.func);
            eprintln!("================");
            eprintln!("Generated assembly for block at pc={pc:#x}:");
            eprintln!("================");
            eprintln!(
                "{}",
                self.codegen_ctx
                    .compiled_code()
                    .unwrap()
                    .disasm
                    .as_ref()
                    .unwrap()
            );
            eprintln!("================");
        }

        // Reset the codegen context after use.
        self.module.clear_context(&mut self.codegen_ctx);

        // Emit jump caches for any newly added jump targets.
        for jump_target in new_jump_targets {
            self.emit_jump_cache(jump_target, self.jump_caches[&jump_target]);
        }

        // Link all the generated code together and resolve references between
        // the function and the jump caches/resolvers.
        self.module.finalize_definitions().unwrap();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(func);

        unsafe { JitFunction(mem::transmute(code)) }
    }

    fn emit_jump_cache(&mut self, target: u32, jump_cache: DataId) {
        // Emit the resolver function first.
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        sig.returns
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        self.codegen_ctx.func.signature = sig;

        let mut builder = FunctionBuilder::new(&mut self.codegen_ctx.func, &mut self.builder_ctx);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        let state_ptr = builder.block_params(entry_block)[0];

        // Store the PC to EmulatorState.
        let pc = builder.ins().iconst(types::I32, target as i64);
        builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            pc,
            state_ptr,
            offset_of!(EmulatorState, pc) as i32,
        );

        // Call lookup_or_translate (it has the same signature as the current
        // function).
        let sigref = builder.import_signature(builder.func.signature.clone());
        let lookup_or_translate = builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            state_ptr,
            offset_of!(EmulatorState, lookup_or_translate) as i32,
        );
        let call = builder
            .ins()
            .call_indirect(sigref, lookup_or_translate, &[state_ptr]);
        let resolved = builder.inst_results(call)[0];

        // Store the returned value to the JUMP_CACHE variable.
        let global = self
            .module
            .declare_data_in_func(jump_cache, &mut builder.func);
        let global = builder
            .ins()
            .symbol_value(self.module.target_config().pointer_type(), global);
        builder
            .ins()
            .store(MemFlags::trusted().with_table(), resolved, global, 0);

        // Return the address of the resolved function.
        builder.ins().return_(&[resolved]);
        builder.finalize();

        // Compile the resolver function.
        let func = self
            .module
            .declare_function(
                &format!("resolver_{target:x}"),
                Linkage::Local,
                &self.codegen_ctx.func.signature,
            )
            .unwrap();
        self.module
            .define_function(func, &mut self.codegen_ctx)
            .unwrap();
        self.module.clear_context(&mut self.codegen_ctx);

        // Emit the JUMP_CACHE variable.
        self.data_ctx
            .define_zeroinit(self.module.target_config().pointer_bytes() as usize);
        let funcref = self.module.declare_func_in_data(func, &mut self.data_ctx);
        self.data_ctx.write_function_addr(0, funcref);
        self.module.define_data(jump_cache, &self.data_ctx).unwrap();
        self.data_ctx.clear();
    }
}

/// Type holding the state needed to generate the Rust code.
struct CraneliftTranslator<'a> {
    builder: FunctionBuilder<'a>,

    module: &'a mut JITModule,

    /// Set of jump targets available in the current module..
    jump_caches: &'a mut FxHashMap<u32, DataId>,

    /// Set of newly added jump targets for which we need to emit a data
    /// section and a resolver stub.
    new_jump_targets: Vec<u32>,

    /// Initial `Value`s assigned to each register at the start of the function.
    /// This `Value` is loaded from the `EmulatorState` structure at the start
    /// of the function.
    initial_reg_values: [Value; 32],

    /// `Value` representing the `state` pointer argument passed to our
    /// function.
    state_ptr: Value,

    /// `Value` representing the base address of the emulated memory space.
    mem_ptr: Value,

    /// The current memory state of the emulator. This is used for fetching
    /// instructions.
    mem: &'a [u8; MEM_SIZE],

    /// Command-line arguments
    args: &'a Args,

    /// Program counter value of the current instruction we are translating.
    pc: u32,

    /// Program counter value of the next instruction that we will translate.
    next_pc: u32,

    /// Whether the last operation on `Trans` was a terminator operation and a
    /// `return` has been emitted in the generated code. If this occurs inside
    /// an `if_val` then this is only true if both branches returned.
    returned: bool,

    /// `Value`s known to be holding a constant. This works because Cranelift's
    /// `Value` type is immutable: each can only have a single definition. We
    /// simply track `Value`s defined using the `iconst` instruction.
    const_values: FxHashMap<Value, u32>,
}

impl CraneliftTranslator<'_> {
    /// Translates instructions starting at at `pc` to Cranelift IR which
    /// mutates `EmulatorState`.
    ///
    /// Returns a list of newly added jump targets for which jump caches and
    /// resolver stubs need to be created.
    fn translate(
        pc: u32,
        mem: &[u8; MEM_SIZE],
        args: &Args,
        module: &mut JITModule,
        builder_ctx: &mut FunctionBuilderContext,
        codegen_ctx: &mut codegen::Context,
        jump_caches: &mut FxHashMap<u32, DataId>,
    ) -> Vec<u32> {
        let mut builder = FunctionBuilder::new(&mut codegen_ctx.func, builder_ctx);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        let state_ptr = builder.block_params(entry_block)[0];
        let mem_ptr = builder.ins().load(
            module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            state_ptr,
            offset_of!(EmulatorState, mem) as i32,
        );

        let mut trans = CraneliftTranslator {
            builder,
            module,
            jump_caches,
            new_jump_targets: vec![],
            initial_reg_values: [Value::new(0); 32],
            state_ptr,
            mem_ptr,
            mem,
            args,
            pc,
            next_pc: 0,
            returned: false,
            const_values: FxHashMap::default(),
        };

        // Declare a variable for each register.
        for i in 0..32 {
            trans.builder.declare_var(trans.reg_var(i), types::I32);
        }

        // Initialize register 0 with a constant 0 value.
        let zero = trans.const_value(0);
        trans.builder.def_var(trans.reg_var(0), zero);
        trans.initial_reg_values[0] = zero;

        // Initialize all other registers with their value from `EmulatorState`.
        // Any loads for registers that are unused will be optimized away by
        // Cranelift.
        for i in 1..32 {
            let val = trans.builder.ins().load(
                types::I32,
                MemFlags::trusted().with_vmctx(),
                trans.state_ptr,
                offset_of!(EmulatorState, regs) as i32 + i as i32 * 4,
            );
            trans.builder.def_var(trans.reg_var(i), val);
            trans.initial_reg_values[i as usize] = val;
        }

        // Translate one instruction at a time until we reach a terminator
        // instruction.
        while !trans.returned {
            translate_one_instruction(&mut trans);
            trans.pc = trans.next_pc;
        }

        trans.builder.finalize();

        trans.new_jump_targets
    }

    /// Returns `Some(n)` if the given `Value` is known to hold a constant. This
    /// is only true for `Value`s generated from the `const_value` method.
    fn extract_const(&self, val: Value) -> Option<u32> {
        self.const_values.get(&val).copied()
    }

    /// Returns a `Variable` for the given register.
    fn reg_var(&self, reg: u32) -> Variable {
        Variable::new(reg as usize)
    }

    /// Write back all modified registers to the `EmulatorState` structure.
    ///
    /// This must be called before returning from the generated function.
    fn flush_modified_registers(&mut self) {
        for i in 1..32 {
            // We only need to write back register values that have changed
            // since they were initialized.
            let val = self.builder.use_var(self.reg_var(i));
            if val == self.initial_reg_values[i as usize] {
                continue;
            }

            self.builder.ins().store(
                MemFlags::trusted().with_vmctx(),
                val,
                self.state_ptr,
                offset_of!(EmulatorState, regs) as i32 + i as i32 * 4,
            );
        }
    }
}

impl Trans for CraneliftTranslator<'_> {
    type Value = Value;

    fn get_reg(&mut self, index: u32) -> Self::Value {
        self.builder.use_var(self.reg_var(index))
    }

    fn set_reg(&mut self, index: u32, val: Self::Value) {
        if index != 0 {
            self.builder.def_var(self.reg_var(index), val);
        }
    }

    fn get_pc(&mut self) -> u32 {
        self.pc
    }

    fn set_next_pc(&mut self, pc: u32) {
        self.next_pc = pc;
    }

    fn fetch_u32(&mut self, address: u32) -> u32 {
        u32::from_le_bytes(read_bytes(&self.mem, address))
    }

    fn const_value(&mut self, x: u32) -> Self::Value {
        let val = self.builder.ins().iconst(types::I32, x as i64);
        self.const_values.insert(val, x);
        val
    }

    fn load(&mut self, width: Width, signed: Signed, address: Self::Value) -> Self::Value {
        let flags = MemFlags::new()
            .with_endianness(Endianness::Little)
            .with_heap()
            .with_notrap();
        let ty = match width {
            Width::Byte => types::I8,
            Width::Half => types::I16,
            Width::Word => types::I32,
        };

        let address = self
            .builder
            .ins()
            .uextend(self.module.target_config().pointer_type(), address);
        let address = self.builder.ins().iadd(self.mem_ptr, address);
        let result = self.builder.ins().load(ty, flags, address, 0);
        match (width, signed) {
            (Width::Word, _) => result,
            (_, Signed::Unsigned) => self.builder.ins().uextend(types::I32, result),
            (_, Signed::Signed) => self.builder.ins().sextend(types::I32, result),
        }
    }

    fn store(&mut self, width: Width, address: Self::Value, val: Self::Value) {
        let flags = MemFlags::new()
            .with_endianness(Endianness::Little)
            .with_heap()
            .with_notrap();
        let ty = match width {
            Width::Byte => types::I8,
            Width::Half => types::I16,
            Width::Word => types::I32,
        };

        let address = self
            .builder
            .ins()
            .uextend(self.module.target_config().pointer_type(), address);
        let address = self.builder.ins().iadd(self.mem_ptr, address);
        let val = match width {
            Width::Word => val,
            _ => self.builder.ins().ireduce(ty, val),
        };
        self.builder.ins().store(flags, val, address, 0);
    }

    fn add(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Some(a), Some(b)) = (self.extract_const(a), self.extract_const(b)) {
            return self.const_value(a.wrapping_add(b));
        }

        self.builder.ins().iadd(a, b)
    }

    fn sub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Some(a), Some(b)) = (self.extract_const(a), self.extract_const(b)) {
            return self.const_value(a.wrapping_sub(b));
        }

        self.builder.ins().isub(a, b)
    }

    fn and(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Some(a), Some(b)) = (self.extract_const(a), self.extract_const(b)) {
            return self.const_value(a & b);
        }

        self.builder.ins().band(a, b)
    }

    fn or(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Some(a), Some(b)) = (self.extract_const(a), self.extract_const(b)) {
            return self.const_value(a | b);
        }

        self.builder.ins().bor(a, b)
    }

    fn xor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Some(a), Some(b)) = (self.extract_const(a), self.extract_const(b)) {
            return self.const_value(a ^ b);
        }

        self.builder.ins().bxor(a, b)
    }

    fn shift_left(&mut self, val: Self::Value, shift: Self::Value) -> Self::Value {
        if let (Some(val), Some(shift)) = (self.extract_const(val), self.extract_const(shift)) {
            return self.const_value(val.wrapping_shl(shift));
        }

        self.builder.ins().ishl(val, shift)
    }

    fn shift_right(&mut self, signed: Signed, val: Self::Value, shift: Self::Value) -> Self::Value {
        if let (Some(val), Some(shift)) = (self.extract_const(val), self.extract_const(shift)) {
            return self.const_value(match signed {
                Signed::Unsigned => val.wrapping_shr(shift),
                Signed::Signed => (val as i32).wrapping_shr(shift) as u32,
            });
        }

        match signed {
            Signed::Unsigned => self.builder.ins().ushr(val, shift),
            Signed::Signed => self.builder.ins().sshr(val, shift),
        }
    }

    fn jump(&mut self, target: Self::Value) {
        self.flush_modified_registers();
        self.returned = true;

        // Block linking optimization: if the jump target is a constant then
        // use a jump cache to cache the lookup.
        if self.args.jit_block_linking {
            if let Some(target) = self.extract_const(target) {
                // Check if a jump cache for this target already exists from
                // previously compiled block. If not then we need to generate
                // a new one.
                let sym = *self.jump_caches.entry(target).or_insert_with(|| {
                    self.new_jump_targets.push(target);
                    self.module
                        .declare_data(
                            &format!("JUMP_CACHE_{target:X}"),
                            Linkage::Local,
                            true,
                            false,
                        )
                        .unwrap()
                });

                // Load the jump cache value and return it.
                let global = self
                    .module
                    .declare_data_in_func(sym, &mut self.builder.func);
                let jump_cache = self
                    .builder
                    .ins()
                    .symbol_value(self.module.target_config().pointer_type(), global);
                let jump_cache = self.builder.ins().load(
                    self.module.target_config().pointer_type(),
                    MemFlags::trusted().with_table(),
                    jump_cache,
                    0,
                );
                self.builder.ins().return_(&[jump_cache]);
                return;
            }
        }

        // Write back PC to EmulatorState.
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            target,
            self.state_ptr,
            offset_of!(EmulatorState, pc) as i32,
        );

        // Load lookup_or_translate from EmulatorState and return it.
        let lookup_or_translate = self.builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, lookup_or_translate) as i32,
        );
        self.builder.ins().return_(&[lookup_or_translate]);
    }

    fn ecall(&mut self) {
        self.flush_modified_registers();

        // Write back PC to EmulatorState.
        let pc = self.builder.ins().iconst(types::I32, self.pc as i64);
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            pc,
            self.state_ptr,
            offset_of!(EmulatorState, pc) as i32,
        );

        // Load ecall_handler from EmulatorState and call it.
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        let sigref = self.builder.import_signature(sig);
        let ecall_handler = self.builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, ecall_handler) as i32,
        );
        self.builder
            .ins()
            .call_indirect(sigref, ecall_handler, &[self.state_ptr]);

        // Load lookup_or_translate from EmulatorState and return it.
        let lookup_or_translate = self.builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, lookup_or_translate) as i32,
        );
        self.builder.ins().return_(&[lookup_or_translate]);
        self.returned = true;
    }

    fn ebreak(&mut self) {
        self.flush_modified_registers();

        // Write back PC to EmulatorState.
        let pc = self.builder.ins().iconst(types::I32, self.pc as i64);
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            pc,
            self.state_ptr,
            offset_of!(EmulatorState, pc) as i32,
        );

        // Load ebreak_handler from EmulatorState and call it.
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        let sigref = self.builder.import_signature(sig);
        let ebreak_handler = self.builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, ebreak_handler) as i32,
        );
        self.builder
            .ins()
            .call_indirect(sigref, ebreak_handler, &[self.state_ptr]);

        // Load lookup_or_translate from EmulatorState and return it.
        let lookup_or_translate = self.builder.ins().load(
            self.module.target_config().pointer_type(),
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, lookup_or_translate) as i32,
        );
        self.builder.ins().return_(&[lookup_or_translate]);
        self.returned = true;
    }

    fn undefined_encoding(&mut self, instr: u32) {
        self.flush_modified_registers();

        // Write back PC to EmulatorState.
        let pc = self.builder.ins().iconst(types::I32, self.pc as i64);
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            pc,
            self.state_ptr,
            offset_of!(EmulatorState, pc) as i32,
        );

        // Load undefined_encoding_handler from EmulatorState and call it.
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        sig.params.push(AbiParam::new(types::I32));
        let sigref = self.builder.import_signature(sig);
        let undefined_encoding_handler = self.builder.ins().load(
            types::I64,
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, undefined_encoding_handler) as i32,
        );
        let instr = self.builder.ins().iconst(types::I32, instr as i64);
        self.builder.ins().call_indirect(
            sigref,
            undefined_encoding_handler,
            &[self.state_ptr, instr],
        );

        // Load lookup_or_translate from EmulatorState and return it.
        let lookup_or_translate = self.builder.ins().load(
            types::I64,
            MemFlags::trusted().with_vmctx(),
            self.state_ptr,
            offset_of!(EmulatorState, lookup_or_translate) as i32,
        );
        self.builder.ins().return_(&[lookup_or_translate]);
        self.returned = true;
    }

    fn if_val(
        &mut self,
        cond: Cond,
        a: Self::Value,
        b: Self::Value,
        if_true: impl FnOnce(&mut Self) -> Self::Value,
        if_false: impl FnOnce(&mut Self) -> Self::Value,
    ) -> Self::Value {
        let true_block = self.builder.create_block();
        let false_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I32);

        let cc = match cond {
            Cond::Eq => IntCC::Equal,
            Cond::Ne => IntCC::NotEqual,
            Cond::Ge(Signed::Signed) => IntCC::SignedGreaterThanOrEqual,
            Cond::Lt(Signed::Signed) => IntCC::SignedLessThan,
            Cond::Ge(Signed::Unsigned) => IntCC::UnsignedGreaterThanOrEqual,
            Cond::Lt(Signed::Unsigned) => IntCC::UnsignedLessThan,
        };
        let cond_value = self.builder.ins().icmp(cc, a, b);
        self.builder.ins().brnz(cond_value, true_block, &[]);
        self.builder.ins().jump(false_block, &[]);

        self.builder.switch_to_block(true_block);
        self.builder.seal_block(true_block);
        assert!(!self.returned);
        let val_true = if_true(self);
        let true_returned = self.returned;
        if !true_returned {
            self.builder.ins().jump(merge_block, &[val_true]);
        }

        self.builder.switch_to_block(false_block);
        self.builder.seal_block(false_block);
        self.returned = false;
        let val_false = if_false(self);
        let false_returned = self.returned;
        if !false_returned {
            self.builder.ins().jump(merge_block, &[val_false]);
        }

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        self.builder.block_params(merge_block)[0]
    }
}
