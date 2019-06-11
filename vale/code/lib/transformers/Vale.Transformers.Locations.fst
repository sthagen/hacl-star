module Vale.Transformers.Locations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

module L = FStar.List.Tot

(* See fsti *)
type location : eqtype =
  | ALocMem : location
  | ALocStack: location
  | ALocReg : reg -> location
  | ALocCf : location
  | ALocOf : location

let locations_of_maddr (m:maddr) : locations =
  match m with
  | MConst _ -> []
  | MReg r _ -> [ALocReg r]
  | MIndex b _ i _ -> [ALocReg b; ALocReg i]

let locations_of_operand64 (o:operand64) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 0 r)], [ALocReg (Reg 0 r)]
  | OMem (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> locations_of_maddr m, [ALocStack]

let locations_of_operand128 (o:operand128) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 1 r)], [ALocReg (Reg 1 r)]
  | OMem (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> locations_of_maddr m, [ALocStack]

private
let both (x: locations & locations) =
  let a, b = x in
  a `L.append` b

let locations_of_explicit (t:instr_operand_explicit) (i:instr_operand_t t) : locations & locations =
  match t with
  | IOp64 -> locations_of_operand64 i
  | IOpXmm -> locations_of_operand128 i

let locations_of_implicit (t:instr_operand_implicit) : locations & locations =
  match t with
  | IOp64One i -> locations_of_operand64 i
  | IOpXmmOne i -> locations_of_operand128 i
  | IOpFlagsCf -> [ALocCf], [ALocCf]
  | IOpFlagsOf -> [ALocOf], [ALocOf]

let rec aux_read_set0 (args:list instr_operand) (oprs:instr_operands_t_args args) : locations =
  match args with
  | [] -> []
  | (IOpEx i) :: args ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t_args args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set0 args r
  | (IOpIm i) :: args ->
    both (locations_of_implicit i) `L.append` aux_read_set0 args (coerce #(instr_operands_t_args args) oprs)

let rec aux_read_set1
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> aux_read_set0 args oprs
  | (Out, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    fst (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (InOut, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (Out, IOpIm i) :: outs ->
    fst (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)
  | (InOut, IOpIm i) :: outs ->
    both (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)

let read_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : locations =
  aux_read_set1 i.outs i.args oprs

let rec aux_write_set
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> []
  | (_, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    snd (locations_of_explicit i l) `L.append` aux_write_set outs args r
  | (_, IOpIm i) :: outs ->
    snd (locations_of_implicit i) `L.append` aux_write_set outs args (coerce #(instr_operands_t outs args) oprs)

let write_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : list location =
  let InstrTypeRecord #outs #args #havoc_flags _ = i in
  let ws = aux_write_set outs args oprs in
  match havoc_flags with
  | HavocFlags -> ALocCf :: ALocOf :: ws
  | PreserveFlags -> ws

(* See fsti *)
let rw_set_of_ins i =
  match i with
  | Instr i oprs _ ->
    read_set i oprs, write_set i oprs
  | Push src t ->
    ALocReg (Reg 0 rRsp) :: both (locations_of_operand64 src),
    [ALocReg (Reg 0 rRsp); ALocStack]
  | Pop dst t ->
    ALocReg (Reg 0 rRsp) :: ALocStack :: fst (locations_of_operand64 dst),
    ALocReg (Reg 0 rRsp) :: snd (locations_of_operand64 dst)
  | Alloc _
  | Dealloc _ ->
    [ALocReg (Reg 0 rRsp)], [ALocReg (Reg 0 rRsp)]

let aux_print_reg_from_location (a:location{ALocReg? a}) : string =
  let ALocReg (Reg file id) = a in
  match file with
  | 0 -> print_reg_name id
  | 1 -> print_xmm id gcc

(* See fsti *)
let disjoint_location a1 a2 =
  match a1, a2 with
  | ALocCf, ALocCf -> ffalse "carry flag not disjoint from itself"
  | ALocOf, ALocOf -> ffalse "overflow flag not disjoint from itself"
  | ALocCf, _ | ALocOf, _ | _, ALocCf | _, ALocOf -> ttrue
  | ALocMem, ALocMem -> ffalse "memory not disjoint from itself"
  | ALocStack, ALocStack -> ffalse "stack not disjoint from itself"
  | ALocMem, ALocStack | ALocStack, ALocMem -> ttrue
  | ALocReg r1, ALocReg r2 ->
    (r1 <> r2) /- ("register " ^ aux_print_reg_from_location a1 ^ " not disjoint from itself")
  | ALocReg _, _ | _, ALocReg _ -> ttrue

(* See fsti *)
let auto_lemma_disjoint_location a1 a2 = ()

(* See fsti *)
let location_val_t a =
  match a with
  | ALocMem -> machine_heap & memTaint_t
  | ALocStack -> machine_stack & memTaint_t
  | ALocReg r -> t_reg r
  | ALocCf -> flag_val_t
  | ALocOf -> flag_val_t

(* See fsti *)
let eval_location a s =
  match a with
  | ALocMem -> s.ms_heap, s.ms_memTaint
  | ALocStack -> s.ms_stack, s.ms_stackTaint
  | ALocReg r -> eval_reg r s
  | ALocCf -> cf s.ms_flags
  | ALocOf -> overflow s.ms_flags

(* See fsti *)
let update_location a v s =
  match a with
  | ALocMem ->
    let v = coerce v in
    { s with ms_heap = fst v ; ms_memTaint = snd v }
  | ALocStack ->
    let v = coerce v in
    { s with ms_stack = fst v ; ms_stackTaint = snd v }
  | ALocReg r ->
    update_reg' r v s
  | ALocCf ->
    { s with ms_flags = FStar.FunctionalExtensionality.on_dom flag (fun f -> if f = fCarry then v else s.ms_flags f) }
  | ALocOf ->
    { s with ms_flags = FStar.FunctionalExtensionality.on_dom flag (fun f -> if f = fOverflow then v else s.ms_flags f) }

(* See fsti *)
let lemma_locations_truly_disjoint a a_change v s = ()

(* See fsti *)
let lemma_locations_complete s1 s2 ok trace =
  let s1, s2 = {s1 with ms_ok = ok ; ms_trace = trace}, {s2 with ms_ok = ok ; ms_trace = trace} in
  assert (s1.ms_ok == s2.ms_ok);
  FStar.Classical.forall_intro (
    (fun r ->
       assert (eval_location (ALocReg r) s1 == eval_location (ALocReg r) s2) (* OBSERVE *)
    ) <: (r:_ -> Lemma (eval_reg r s1 == eval_reg r s2))
  );
  assert (FStar.FunctionalExtensionality.feq s1.ms_regs s2.ms_regs);
  assert (s1.ms_regs == s2.ms_regs);
  assert (overflow s1.ms_flags == overflow s2.ms_flags);
  assert (cf s1.ms_flags == cf s2.ms_flags);
  assume (s1.ms_flags == s2.ms_flags); (* WARN UNSOUND!!! REVIEW: Figure out how to fix this. *)
  assert (s1.ms_heap == s2.ms_heap);
  assert (s1.ms_memTaint == s2.ms_memTaint);
  assert (s1.ms_stack == s2.ms_stack);
  assert (s1.ms_stackTaint == s2.ms_stackTaint);
  assert (s1.ms_trace == s2.ms_trace)