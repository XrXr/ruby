module RubyVM::MJIT
  #  ec: rdi
  # cfp: rsi
  #  sp: rbx
  # scratch regs: rax
  class InsnCompiler
    # 3/101

    # nop
    # getlocal
    # setlocal
    # getblockparam
    # setblockparam
    # getblockparamproxy
    # getspecial
    # setspecial
    # getinstancevariable
    # setinstancevariable
    # getclassvariable
    # setclassvariable
    # opt_getconstant_path
    # getconstant
    # setconstant
    # getglobal
    # setglobal

    # @param jit [RubyVM::MJIT::JITState]
    # @param ctx [RubyVM::MJIT::Context]
    # @param asm [RubyVM::MJIT::X86Assembler]
    def putnil(jit, ctx, asm)
      asm.mov([SP, C.VALUE.size * ctx.stack_size], Qnil)
      ctx.stack_size += 1
      KeepCompiling
    end

    # putself
    # putobject
    # putspecialobject
    # putstring
    # concatstrings
    # anytostring
    # toregexp
    # intern
    # newarray
    # newarraykwsplat
    # duparray
    # duphash
    # expandarray
    # concatarray
    # splatarray
    # newhash
    # newrange
    # pop
    # dup
    # dupn
    # swap
    # opt_reverse
    # topn
    # setn
    # adjuststack
    # defined
    # checkmatch
    # checkkeyword
    # checktype
    # defineclass
    # definemethod
    # definesmethod
    # send
    # opt_send_without_block
    # objtostring
    # opt_str_freeze
    # opt_nil_p
    # opt_str_uminus
    # opt_newarray_max
    # opt_newarray_min
    # invokesuper
    # invokeblock

    # @param jit [RubyVM::MJIT::JITState]
    # @param ctx [RubyVM::MJIT::Context]
    # @param asm [RubyVM::MJIT::X86Assembler]
    def leave(jit, ctx, asm)
      assert_eq!(ctx.stack_size, 1)

      asm.comment('RUBY_VM_CHECK_INTS(ec)')
      asm.mov(:eax, [EC, C.rb_execution_context_t.offsetof(:interrupt_flag)])
      asm.test(:eax, :eax)
      asm.jz(not_interrupted = asm.new_label(:not_interrupted))
      Compiler.compile_exit(jit, ctx, asm) # TODO: use ocb
      asm.write_label(not_interrupted)

      asm.comment('pop stack frame')
      asm.add(CFP, C.rb_control_frame_t.size) # cfp = cfp + 1
      asm.mov([EC, C.rb_execution_context_t.offsetof(:cfp)], CFP) # ec->cfp = cfp

      # Return a value
      asm.mov(:rax, [SP])

      # Restore callee-saved registers
      asm.pop(SP)

      asm.ret
      EndBlock
    end

    # throw
    # jump
    # branchif
    # branchunless
    # branchnil
    # once
    # opt_case_dispatch
    # opt_plus
    # opt_minus
    # opt_mult
    # opt_div
    # opt_mod
    # opt_eq
    # opt_neq
    # opt_lt
    # opt_le
    # opt_gt
    # opt_ge
    # opt_ltlt
    # opt_and
    # opt_or
    # opt_aref
    # opt_aset
    # opt_aset_with
    # opt_aref_with
    # opt_length
    # opt_size
    # opt_empty_p
    # opt_succ
    # opt_not
    # opt_regexpmatch2
    # invokebuiltin
    # opt_invokebuiltin_delegate
    # opt_invokebuiltin_delegate_leave

    # @param jit [RubyVM::MJIT::JITState]
    # @param ctx [RubyVM::MJIT::Context]
    # @param asm [RubyVM::MJIT::X86Assembler]
    def getlocal_WC_0(jit, ctx, asm)
      # Get operands
      idx = jit.operand(0)
      level = 0

      # Get EP
      asm.mov(:rax, [CFP, C.rb_control_frame_t.offsetof(:ep)])

      # Get a local variable
      asm.mov(:rax, [:rax, -idx * C.VALUE.size])

      # Push it to the stack
      asm.mov([SP, C.VALUE.size * ctx.stack_size], :rax)
      ctx.stack_size += 1
      KeepCompiling
    end

    # getlocal_WC_1
    # setlocal_WC_0
    # setlocal_WC_1
    # putobject_INT2FIX_0_
    # putobject_INT2FIX_1_

    private

    def assert_eq!(left, right)
      if left != right
        raise "'#{left.inspect}' was not '#{right.inspect}'"
      end
    end
  end
end