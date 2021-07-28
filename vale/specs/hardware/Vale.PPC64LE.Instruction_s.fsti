module Vale.PPC64LE.Instruction_s
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.PPC64LE.Machine_s

(*
An generic instruction has:
- zero or more input operands
- zero or more output operands
- a possible effect on the branch facility registers
Some of the operands may be hard-coded to a particular register; some operands are optional; 
other operands are flexible.
*)
type instr_operand_inout = | In | Out
type instr_operand_explicit = // flexible operand
  | IOpGpr : instr_operand_explicit
  | IOpVec : instr_operand_explicit
  | IOpVsx : instr_operand_explicit
type instr_operand_implicit = // hard-coded operand
  | IOpCr0 : instr_operand_implicit
  | IOpCtr : instr_operand_implicit
type instr_operand_optional = // optional operand
  | IOpCr : instr_operand_optional
type instr_operand =
  | IOpEx : instr_operand_explicit -> instr_operand
  | IOpIm : instr_operand_implicit -> instr_operand
  | IOpOpt : instr_operand_optional -> instr_operand
let instr_out = instr_operand_inout & instr_operand

irreducible let instr_attr = ()
unfold let normal (#a:Type) (x:a) : a = norm [zeta; iota; delta_attr [`%instr_attr]] x

let arrow (a b:Type) = a -> b

[@instr_attr] unfold let in (o:instr_operand) = (In, o)
[@instr_attr] unfold let out (o:instr_operand) = (Out, o)
[@instr_attr] unfold let opGpr = IOpEx IOpGpr
[@instr_attr] unfold let opVec = IOpEx IOpVec
[@instr_attr] unfold let opVsx = IOpEx IOpVsx
[@instr_attr] unfold let opCr0 = IOpIm IOpCr0
[@instr_attr] unfold let opCtr = IOpIm IOpCtr
[@instr_attr] unfold let opCr = IOpOpt IOpCr

[@instr_attr]
let instr_val_t (o:instr_operand) : Type0 =
  match o with
  | IOpEx IOpGpr -> nat64
  | IOpEx IOpVec -> nat128
  | IOpEx IOpVsx -> nat128
  | IOpIm IOpCr0 -> fixed_point_flag
  | IOpIm IOpCtr -> nat64
  | IOpIm IOpCr -> condition_register

[@instr_attr]
let rec instr_ret_t (outs:list instr_out) : Type0 =
  match outs with
  | [] -> unit
  | [(_, o)] -> instr_val_t o
  | (_, o)::outs -> instr_val_t o & instr_ret_t outs

[@instr_attr]
let rec instr_args_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match args with
  | [] -> option (instr_ret_t outs)
  | i::args -> arrow (instr_val_t i) (instr_args_t outs args)

[@instr_attr]
let rec instr_inouts_t (outs inouts:list instr_out) (args:list instr_operand) : Type0 =
  match inouts with
  | [] -> instr_args_t outs args
  | (Out, _)::inouts -> instr_inouts_t outs inouts args
  | (In, i)::inouts -> arrow (instr_val_t i) (instr_inouts_t outs inouts args)

(*
An instr evaluator is a function of type:
  in_outs1 ... ->  in_outsi -> args1 -> ...> argsj -> (outs1 & (... & outsk) ...)
where in_outs = [(b, o) in outs | b = In]
*)
[@instr_attr]
let instr_eval_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  instr_inouts_t outs outs args

[@instr_attr]
let instr_operand_t (arg:instr_operand_explicit) : Type0 =
  match arg with
  | IOpGpr -> operand64
  | IOpVec -> operand128
  | IOpVsx -> operand128

[@instr_attr]
let rec instr_operands_t_args (args:list instr_operand) : Type0 =
  match args with
  | [] -> unit
  | (IOpEx i)::args -> instr_operand_t i & instr_operands_t_args args
  | (IOpIm _)::args -> instr_operands_t_args args
  | (IOpOpt _)::args -> instr_operands_t_args args

[@instr_attr]
let rec instr_operands_t (outs:list instr_out) (args:list instr_operand) : Type0 =
  match outs with
  | [] -> instr_operands_t_args args
  | (_, IOpEx i)::outs -> instr_operand_t i & instr_operands_t outs args
  | (_, IOpIm _)::outs -> instr_operands_t outs args
  | (_, IOpOpt _)::outs -> instr_operands_t outs args

type instr_print_operand =
  | PGpr : operand64 -> instr_print_operand
  | PVec : operand128 -> instr_print_operand
  | PVsx : operand128 -> instr_print_operand
  | PImm : int16 -> instr_print_operand
  | PShift : imm_shift -> instr_print_operand
type instr_print =
  | Print : string -> instr_print_kind -> list instr_print_operand -> instr_print

type flag_havoc = | HavocFlags | PreserveFlags

val instr_t (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc) : Type0

noeq type instr_t_record =
  | InstrTypeRecord :
      #outs:list instr_out ->
      #args:list instr_operand ->
      #havoc_flags:flag_havoc ->
      i:instr_t outs args havoc_flags ->
      instr_t_record

val instr_eval
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags)
  : norm [zeta; iota; delta_attr [`%instr_attr]] (instr_eval_t outs args)

val instr_printer
    (#outs:list instr_out) (#args:list instr_operand) (#havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags) (oprs:normal (instr_operands_t outs args))
  : instr_print

let instr_dep
    (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc)
    (f:normal (instr_eval_t outs args))
  : Type0 =
  i:(instr_t outs args havoc_flags){instr_eval i == f}
