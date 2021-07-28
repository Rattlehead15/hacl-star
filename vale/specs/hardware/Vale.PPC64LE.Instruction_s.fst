module Vale.PPC64LE.Instruction_s
open FStar.Mul

[@instr_attr]
let rec instr_print_t_args (args:list instr_operand) : Type0 =
  match args with
  | [] -> instr_print
  | (IOpEx i)::args -> arrow (instr_operand_t i) (instr_print_t_args args)
  | (IOpIm _)::args -> instr_print_t_args args
  | (IOpOpt _)::args -> instr_print_t_args args

[@instr_attr]
let rec instr_print_t (outs:list instr_operand_inout) (args:list instr_operand) : Type0 =
  match outs with
  | [] -> instr_print_t_args args
  | (_, IOpEx i)::outs -> arrow (instr_operand_t i) (instr_print_t outs args)
  | (_, IOpIm _)::outs -> instr_print_t outs args
  | (_, IOpOpt _)::outs -> instr_print_t outs args

noeq type instr_t (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc) = {
  i_eval:instr_eval_t outs args;
  i_printer:instr_print_t outs args;
}

let make_ins
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (#f:normal (instr_eval_t outs args))
    (print:normal (instr_print_t outs args))
  : instr_dep outs args havoc_flags f =
  {i_printer = print; i_eval = f}

let print (name:string) (oprs:list instr_print_operand) : instr_print = Print name POpcode oprs
let print_s (name:string) (oprs:list instr_print_operand) : instr_print = Print name PSuffix oprs
