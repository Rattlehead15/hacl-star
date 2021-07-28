module Vale.PPC64LE.Machine_s
open FStar.Mul

type condition_register =
  | Cr0 : condition_register
  | Cr1 : condition_register
  | Cr2 : condition_register
  | Cr3 : condition_register
  | Cr4 : condition_register
  | Cr5 : condition_register
  | Cr6 : condition_register
  | Cr7 : condition_register

type fixed_point_flag = {
  f_lt:bool;      // negative
  f_gt:bool;      // positive
  f_eq:bool;      // zero
  f_so:bool       // summary overflow
}

let int16 = Lib.IntTypes.int16
unfold let nat64 = Vale.Def.Types_s.nat64
unfold let nat128 = Vale.Def.Words_s.nat128

let n_reg_files = 3
let reg_file_id = rf:nat{rf < n_reg_files}
let n_regs (rf:reg_file_id) : nat =
  match rf with
  | 0 -> 32
  | 1 -> 16
  | 1 -> 32
let t_reg_file (rf:reg_file_id) : Type0 =
  match rf with
  | 0 -> nat64
  | 1 -> nat128
  | 2 -> nat128

let reg_id (rf:reg_file_id) : Type0 = r:nat{r < n_regs rf}

irreducible let va_qattr = ()

[@va_qattr]
type reg =
  | Reg: rf:reg_file_id -> r:reg_id rf -> reg

let t_reg (r:reg) : Type0 = t_reg_file r.rf

type maddr:eqtype =
  | MReg: ra:reg -> ds:int -> maddr
  | MIndex: ra:reg -> rb:reg -> maddr

let imm_shift : Type0 = i:nat{i < 64}

type imm:eqtype =
  | IValue: i:int16 -> imm
  | IShift: i:imm_shift -> imm

[@va_qattr]
type operand (tr:eqtype) : eqtype =
  | OImm: i:imm -> operand tr
  | OReg: r:tr -> operand tr
  | OMem: m:maddr -> operand tr

[@va_qattr]
let operand_rf (rf:reg_file_id) : eqtype =
  operand (reg_id rf)

[@va_qattr]
unfold let oreg (r:reg) : operand_rf r.rf =
  OReg r.r

let reg_gp : Type0 = r:nat{r < 32}
let reg_vec : Type0 = r:nat{r < 16}

[@va_qattr] unfold let r0 : reg_gp = 0
[@va_qattr] unfold let r1 : reg_gp = 1
[@va_qattr] unfold let r2 : reg_gp = 2
[@va_qattr] unfold let r3 : reg_gp = 3
[@va_qattr] unfold let r4 : reg_gp = 4
[@va_qattr] unfold let r5 : reg_gp = 5
[@va_qattr] unfold let r6 : reg_gp = 6
[@va_qattr] unfold let r7 : reg_gp = 7
[@va_qattr] unfold let r8 : reg_gp = 8
[@va_qattr] unfold let r9 : reg_gp = 9
[@va_qattr] unfold let r10 : reg_gp = 10
[@va_qattr] unfold let r11 : reg_gp = 11
[@va_qattr] unfold let r12 : reg_gp = 12
[@va_qattr] unfold let r13 : reg_gp = 13
[@va_qattr] unfold let r14 : reg_gp = 14
[@va_qattr] unfold let r15 : reg_gp = 15
[@va_qattr] unfold let r16 : reg_gp = 16
[@va_qattr] unfold let r17 : reg_gp = 17
[@va_qattr] unfold let r18 : reg_gp = 18
[@va_qattr] unfold let r19 : reg_gp = 19
[@va_qattr] unfold let r20 : reg_gp = 20
[@va_qattr] unfold let r21 : reg_gp = 21
[@va_qattr] unfold let r22 : reg_gp = 22
[@va_qattr] unfold let r23 : reg_gp = 23
[@va_qattr] unfold let r24 : reg_gp = 24
[@va_qattr] unfold let r25 : reg_gp = 25
[@va_qattr] unfold let r26 : reg_gp = 26
[@va_qattr] unfold let r27 : reg_gp = 27
[@va_qattr] unfold let r28 : reg_gp = 28
[@va_qattr] unfold let r29 : reg_gp = 29
[@va_qattr] unfold let r30 : reg_gp = 30
[@va_qattr] unfold let r31 : reg_gp = 31

[@va_qattr] unfold let reg_r0 : reg = Reg 0 0
[@va_qattr] unfold let reg_r1 : reg = Reg 0 1
[@va_qattr] unfold let reg_r2 : reg = Reg 0 2
[@va_qattr] unfold let reg_r3 : reg = Reg 0 3
[@va_qattr] unfold let reg_r4 : reg = Reg 0 4
[@va_qattr] unfold let reg_r5 : reg = Reg 0 5
[@va_qattr] unfold let reg_r6 : reg = Reg 0 6
[@va_qattr] unfold let reg_r7 : reg = Reg 0 7
[@va_qattr] unfold let reg_r8  : reg = Reg 0 8
[@va_qattr] unfold let reg_r9  : reg = Reg 0 9
[@va_qattr] unfold let reg_r10 : reg = Reg 0 10
[@va_qattr] unfold let reg_r11 : reg = Reg 0 11
[@va_qattr] unfold let reg_r12 : reg = Reg 0 12
[@va_qattr] unfold let reg_r13 : reg = Reg 0 13
[@va_qattr] unfold let reg_r14 : reg = Reg 0 14
[@va_qattr] unfold let reg_r15 : reg = Reg 0 15
[@va_qattr] unfold let reg_r16 : reg = Reg 0 16
[@va_qattr] unfold let reg_r17 : reg = Reg 0 17
[@va_qattr] unfold let reg_r18 : reg = Reg 0 18
[@va_qattr] unfold let reg_r19 : reg = Reg 0 19
[@va_qattr] unfold let reg_r20 : reg = Reg 0 20
[@va_qattr] unfold let reg_r21 : reg = Reg 0 21
[@va_qattr] unfold let reg_r22 : reg = Reg 0 22
[@va_qattr] unfold let reg_r23 : reg = Reg 0 23
[@va_qattr] unfold let reg_r24  : reg = Reg 0 24
[@va_qattr] unfold let reg_r25  : reg = Reg 0 25
[@va_qattr] unfold let reg_r26 : reg = Reg 0 26
[@va_qattr] unfold let reg_r27 : reg = Reg 0 27
[@va_qattr] unfold let reg_r28 : reg = Reg 0 28
[@va_qattr] unfold let reg_r29 : reg = Reg 0 29
[@va_qattr] unfold let reg_r30 : reg = Reg 0 30
[@va_qattr] unfold let reg_r31 : reg = Reg 0 31

[@va_qattr]
let operand64:eqtype = operand reg_gp

[@va_qattr]
let operand128:eqtype = operand reg_vec
