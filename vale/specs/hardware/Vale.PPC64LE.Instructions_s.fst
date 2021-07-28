module Vale.PPC64LE.Instructions_s
open FStar.Mul
friend Vale.PPC64LE.Instruction_s

let ins_Load64 = make_ins (fun rt ra -> print_s "ld" [PGpr rt; PGpr ra])

let ins_LoadRev64 = make_ins (fun rt ra rb -> print_s "ldbrx" [PGpr rt; PGpr ra; PGpr rb])

let ins_ByteRev64 = make_ins (fun ra rs -> print_s "brd" [PGpr ra; PGpr rs])

let ins_SetRegLT = make_ins (fun rx ry rz -> print_s "isellt" [PGpr rx; PGpr ry; PGpr rz])

let ins_Add = make_ins (fun rt ra rb -> print_s "add" [PGpr rt; PGpr ra; PGpr rb])

let ins_AddCarry = make_ins (fun rt ra rb -> print_s "addc" [PGpr rt; PGpr ra; PGpr rb])

let ins_Sub = make_ins (fun rt ra rb -> print_s "sub" [PGpr rt; PGpr ra; PGpr rb])

let ins_SubCarry = make_ins (fun rt ra rb -> print_s "subc" [PGpr rt; PGpr ra; PGpr rb])

let ins_And = make_ins (fun rt rs rb -> print_s "and" [PGpr rt; PGpr rs; PGpr rb])

let ins_Xor = make_ins (fun rt rs rb -> print_s "xor" [PGpr rt; PGpr rs; PGpr rb])

let ins_SRImm64 = make_ins (fun rx ry n -> print_s "srdi" [PGpr rx; PGpr ry; PImm n])

let ins_SLImm64 = make_ins (fun rx ry n -> print_s "sldi" [PGpr rx; PGpr ry; PImm n])

let MulLow32 = make_ins (fun rt ra rb -> print_s "mullw" [PGpr rt; PGpr ra; PGpr rb])

let MulHigh32 = make_ins (fun rt ra rb -> print_s "mulhw" [PGpr rt; PGpr ra; PGpr rb])
