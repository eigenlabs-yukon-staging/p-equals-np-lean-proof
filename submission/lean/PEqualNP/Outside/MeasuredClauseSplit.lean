import PEqualNP.Outside.ParsimoniousClauseSplit
import PEqualNP.Outside.SatCodePrimitives
import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Library.SearchHelpers.SearchToDecision
import PEqualNP.Library.Machines.IterMeasure

namespace PEqualNP.Outside.CNFWidth
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Library.SearchHelpers.S2D
  (incB bits_succ incB_length cpt_incB dig cpt_dig)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun s : Word => s) (fun s : Word => s)

def raw (r : Word) : Word := sel (bflag (isEnd r)) (headI r) []
def advance (r : Word) : Word := sel (bflag (isEnd r)) (dropI r) r

theorem raw_cpt : CPT raw := cpt_sel cpt_isEndF cpt_headI (cpt_const [])
theorem advance_cpt : CPT advance := cpt_sel cpt_isEndF cpt_dropI cpt_id

theorem advance_partition (r : Word) : raw r ++ advance r = r := by
  cases h : isEnd r <;> simp [raw,advance,sel,bflag,h,headI_dropI]

def evenLit (neg : Bool) (r : Word) : Word :=
  let sign := if neg then !polB r else polB r
  let tail := r.tail.tail
  sel r [] ([true,sign] ++ sel (bflag (tail.headD false)) [] [true,false] ++ tail)

theorem sign_cpt : CPT (fun r : Word => bflag (polB r)) := by
  exact cptl (cpt_comp (cpt_tail1 cpt_id) cpt_firstF) (fun r => by
    cases r with
    | nil => rfl
    | cons a r => cases r <;> rfl)

theorem evenLit_cpt (neg : Bool) : CPT (evenLit neg) := by
  have s : CPT (fun r : Word => [true, if neg then !polB r else polB r]) := by
    cases neg
    · exact cptl (cpt_sel sign_cpt (cpt_const [true,false]) (cpt_const [true,true]))
        (fun r => by cases polB r <;> rfl)
    · exact cptl (cpt_sel sign_cpt (cpt_const [true,true]) (cpt_const [true,false]))
        (fun r => by cases polB r <;> rfl)
  have t := cpt_tail1 (cpt_tail1 cpt_id)
  have f := cpt_comp t cpt_firstF
  have pre := cpt_sel f (cpt_const []) (cpt_const [true,false])
  exact cptl (cpt_sel cpt_id (cpt_const []) (cpt_app2 (cpt_app2 s pre) t)) (fun _ => rfl)

theorem evenLit_len (neg : Bool) (r : Word) : (evenLit neg r).length ≤ r.length+4 := by
  have htail : r.tail.tail.length ≤ r.length := by
    simp only [List.length_tail]
    omega
  have hpre : (sel (bflag (r.tail.tail.headD false)) [] [true,false]).length ≤ 2 := by
    unfold sel
    split <;> decide
  unfold evenLit
  dsimp only
  rw [sel]
  split
  · simp
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem evenLit_enc (neg : Bool) (l : Literal) :
    evenLit neg (encodeLiteral l) =
      encodeLiteral (2*l.1, if neg then !l.2 else l.2) := by
  obtain ⟨i,b⟩ := l
  by_cases hi : i = 0
  · subst i
    cases neg <;> cases b <;> rfl
  · have hb : i.bits ≠ [] := by
      intro he
      exact hi (by simpa [he] using (PEqualNP.Library.SearchHelpers.bits_injective (a₁ := i) (a₂ := 0) (by simp [he])))
    rw [show encodeLiteral (i,b) =
      true :: b :: (i.bits.flatMap fun d => [true,d]) ++ [false,true] by rfl]
    simp only [encodeLiteral,Prod.fst,Prod.snd,Nat.bit0_bits _ hi,List.flatMap_cons,
      List.cons_append,List.nil_append]
    rcases hbits : i.bits with _ | ⟨d,ds⟩
    · exact False.elim (hb hbits)
    · cases neg <;> cases b <;>
        simp [evenLit,polB,sel,bflag,List.flatMap_cons]

def oddLit (pol : Bool) (n : Word) : Word := [true,pol,true,true] ++ dig n ++ [false,true]

theorem oddLit_cpt (pol : Bool) : CPT (oddLit pol) :=
  cptl (cpt_app2 (cpt_app2 (cpt_const [true,pol,true,true]) cpt_dig) (cpt_const [false,true]))
    (fun _ => rfl)

theorem oddLit_enc (pol : Bool) (n : ℕ) :
    oddLit pol n.bits = encodeLiteral (fresh n, pol) := by
  simp [oddLit,encodeLiteral,fresh,Nat.bit1_bits,dig]

theorem oddLit_len (pol : Bool) (n : Word) : (oddLit pol n).length = 2*n.length+6 := by
  have k (x : Word) : (dig x).length = 2*x.length := by
    induction x with
    | nil => rfl
    | cons b x ih => simp [dig,ih]; omega
  simp [oddLit,k]


def shortBlock (a b c d : Word) : Word :=
  evenLit false a ++ evenLit false b ++ evenLit false c ++ evenLit false d ++ [false,false]

def longBlock (n a b c d : Word) : Word :=
  let A := evenLit false a
  let B := evenLit false b
  let C := evenLit false c
  let D := evenLit false d
  let neg := oddLit false n
  let pos := oddLit true n
  A ++ B ++ neg ++ [false,false] ++
    evenLit true a ++ pos ++ [false,false] ++
    evenLit true b ++ pos ++ [false,false] ++
    pos ++ C ++ D ++ [false,false]

def block (n a b c d : Word) : Word :=
  sel d (shortBlock a b c d) (longBlock n a b c d)

theorem append_cpt (fs : List (Word → Word)) (h : ∀ f ∈ fs, CPT f) :
    CPT (fun x => fs.flatMap fun f => f x) := by
  induction fs with
  | nil => exact cpt_const []
  | cons f fs ih =>
    exact cpt_app2 (h f (List.mem_cons_self ..))
      (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem block_cpt {n a b c d : Word → Word} (hn : CPT n) (ha : CPT a)
    (hb : CPT b) (hc : CPT c) (hd : CPT d) :
    CPT (fun x => block (n x) (a x) (b x) (c x) (d x)) := by
  let A := fun x => evenLit false (a x)
  let B := fun x => evenLit false (b x)
  let C := fun x => evenLit false (c x)
  let D := fun x => evenLit false (d x)
  let A' := fun x => evenLit true (a x)
  let B' := fun x => evenLit true (b x)
  let N := fun x => oddLit false (n x)
  let P := fun x => oddLit true (n x)
  let E : Word → Word := fun _ => [false,false]
  have hs := append_cpt [A,B,C,D,E] (by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro f hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact cpt_comp ha (evenLit_cpt false)
    · exact cpt_comp hb (evenLit_cpt false)
    · exact cpt_comp hc (evenLit_cpt false)
    · exact cpt_comp hd (evenLit_cpt false)
    · exact cpt_const _)
  have hl := append_cpt [A,B,N,E,A',P,E,B',P,E,P,C,D,E] (by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro f hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first | exact cpt_const _ | exact cpt_comp ha (evenLit_cpt _) |
      exact cpt_comp hb (evenLit_cpt _) | exact cpt_comp hc (evenLit_cpt _) |
      exact cpt_comp hd (evenLit_cpt _) | exact cpt_comp hn (oddLit_cpt _))
  apply cptl (cpt_sel hd hs hl)
  intro x
  simp only [block,shortBlock,longBlock,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.append_assoc,A,B,C,D,A',B',N,P,E]

theorem block_len (n a b c d : Word) :
    (block n a b c d).length ≤ 2*(a.length+b.length+c.length+d.length) + 8*n.length+56 := by
  have hA := evenLit_len false a
  have hB := evenLit_len false b
  have hC := evenLit_len false c
  have hD := evenLit_len false d
  have hA' := evenLit_len true a
  have hB' := evenLit_len true b
  unfold block sel
  split <;> simp only [shortBlock,longBlock,oddLit_len,List.length_append,
    List.length_cons,List.length_nil] <;> omega


def rest (s : Word) := (unpairB s).1
def index (s : Word) := (unpairB (unpairB s).2).1
def result (s : Word) := (unpairB (unpairB s).2).2

def pack (r n o : Word) := pairB r (pairB n o)

def pass (r : Word) := dropI (advance (advance (advance (advance r))))

def step (s : Word) : Word :=
  let r := rest s
  let a := advance r
  let b := advance a
  let c := advance b
  let n := index s
  sel r s (pack (pass r) (incB n) (result s ++ block n (raw r) (raw a) (raw b) (raw c)))

theorem step_cpt : CPT step := by
  have ha := advance_cpt
  have hr := cpt_unpairB1
  have h1 := cpt_comp hr ha
  have h2 := cpt_comp h1 ha
  have h3 := cpt_comp h2 ha
  have h4 := cpt_comp h3 ha
  have hn := cpt_unpairB1_1 cpt_unpairB2
  have ho := cpt_unpairB2_1 cpt_unpairB2
  have hb := block_cpt hn (cpt_comp hr raw_cpt) (cpt_comp h1 raw_cpt)
    (cpt_comp h2 raw_cpt) (cpt_comp h3 raw_cpt)
  have hpass := cpt_comp h4 cpt_dropI
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 hpass
    (cpt_pairB2 (cpt_comp hn cpt_incB) (cpt_app2 ho hb)))) (fun _ => rfl)

theorem headI_nonempty {r : Word} (hr : r ≠ []) : headI r ≠ [] := by
  rcases r with _ | ⟨a,_ | ⟨b,r⟩⟩
  · contradiction
  · simp [headI]
  · cases a <;> simp [headI]

theorem dropI_lt {r : Word} (hr : r ≠ []) : (dropI r).length < r.length := by
  have h := congrArg List.length (headI_dropI r)
  have hne := headI_nonempty hr
  simp only [List.length_append] at h
  have := List.length_pos_iff.mpr hne
  omega

theorem advance_length (r : Word) :
    (raw r).length + (advance r).length = r.length := by
  simpa only [List.length_append] using congrArg List.length (advance_partition r)

theorem pass_decreases {r : Word} (hr : r ≠ []) : (pass r).length < r.length := by
  have h1 := advance_length r
  have h2 := advance_length (advance r)
  have h3 := advance_length (advance (advance r))
  have h4 := advance_length (advance (advance (advance r)))
  unfold pass
  by_cases hs : advance (advance (advance (advance r))) = []
  · rw [hs]
    exact List.length_pos_iff.mpr hr
  · have := dropI_lt hs
    omega

def growth (s : Word) := 12*((rest s).length+(index s).length)+64

theorem measure_bounds (s : Word) :
    2*(rest s).length + 2*(index s).length + (result s).length ≤ s.length := by
  have h := unpairB_length s
  have h' := unpairB_length (unpairB s).2
  dsimp [rest,index,result]
  omega

theorem growth_invariant (s : Word) : growth (step s) ≤ growth s := by
  by_cases hr : rest s = []
  · simp [step,sel,hr]
  · have hp := pass_decreases hr
    have hn := incB_length (index s)
    rw [step, sel, ite_eq_right hr]
    simp only [growth,pack,rest,index,unpairB_pairB] at *
    omega

theorem growth_length (s : Word) : (step s).length ≤ s.length + growth s := by
  by_cases hr : rest s = []
  · simp [step,sel,hr]
  · have hm := measure_bounds s
    have hp := pass_decreases hr
    have hn := incB_length (index s)
    let r := rest s
    let a := advance r
    let b := advance a
    let c := advance b
    have hl := block_len (index s) (raw r) (raw a) (raw b) (raw c)
    have h1 := advance_length r
    have h2 := advance_length a
    have h3 := advance_length b
    have h4 := advance_length c
    rw [step, sel, ite_eq_right hr]
    change (pack (pass r) (incB (index s))
      (result s ++ block (index s) (raw r) (raw a) (raw b) (raw c))).length ≤ _
    simp only [pack,pairB_length,List.length_append,growth]
    change _ ≤ s.length + (12*(r.length+(index s).length)+64)
    change (pass r).length < r.length at hp
    change 2*r.length + 2*(index s).length + (result s).length ≤ s.length at hm
    change (raw r).length + a.length = r.length at h1
    change (raw a).length + b.length = a.length at h2
    change (raw b).length + c.length = b.length at h3
    omega

def run (r : Word) : Word := result (step^[r.length] (pack r [] []))

theorem run_cpt : CPT run := by
  obtain ⟨m⟩ := step_cpt
  have iter := Iter.iter_polyTime_measure step m growth 64 growth_invariant growth_length
    (fun s => by have h := measure_bounds s; unfold growth; omega)
  have hpack : CPT (fun r => pack r [] []) :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) (cpt_const []))
  have hout : CPT result := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pair hpack cpt_id) iter) hout) (fun _ => rfl)


theorem raw_lit (l : Literal) (r : Word) : raw (encodeLiteral l ++ r) = encodeLiteral l := by
  simp [raw,isEnd_lit,sel,bflag,headI_lit]

theorem advance_lit (l : Literal) (r : Word) : advance (encodeLiteral l ++ r) = r := by
  simp [advance,isEnd_lit,sel,bflag,dropI_lit]

theorem raw_close (r : Word) : raw (false :: false :: r) = [] := rfl
theorem advance_close (r : Word) : advance (false :: false :: r) = false :: false :: r := rfl

@[simp] theorem encodeLiteral_nonempty (l : Literal) : encodeLiteral l ≠ [] := by
  simp [encodeLiteral]

theorem step_close (cl : Clause) (hcl : cl.length ≤ 4) (r o : Word) (n : ℕ) :
    step (pack (encodeClause cl ++ r) n.bits o) =
      pack r (n+1).bits (o ++ encodeCNF (splitClause n cl)) := by
  have hnon : encodeClause cl ++ r ≠ [] := by simp [encodeClause]
  have hb := (bits_succ n).symm
  simp only [step,rest,index,result,pack,unpairB_pairB,sel,if_neg hnon,hb]
  congr 1
  · match cl with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] =>
      simp [pass,encodeClause,List.flatMap_cons,List.append_assoc,advance_lit,advance_close,dropI]
    | _::_::_::_::_::_ =>
      simp only [List.length_cons] at hcl
      omega
  · congr 1
    congr 1
    match cl with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] =>
      simp [encodeCNF,encodeClause,List.flatMap_cons,List.append_assoc,advance_lit,advance_close,
        raw_lit,raw_close,block,shortBlock,longBlock,splitClause,liftLit,evenLit_enc,
        oddLit_enc,sel,show evenLit false [] = [] by rfl]
    | _::_::_::_::_::_ =>
      simp only [List.length_cons] at hcl
      omega

def splitFrom (j : ℕ) : CNF → CNF
  | [] => []
  | cl :: F => splitClause j cl ++ splitFrom (j+1) F

theorem splitFrom_range (j : ℕ) (F : CNF) :
    splitFrom j F = (List.range F.length).flatMap fun i => splitClause (j+i) (F[i]?.getD []) := by
  induction F generalizing j with
  | nil => simp [splitFrom]
  | cons cl F ih =>
    rw [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,splitFrom,ih]
    congr 1
    apply List.flatMap_congr
    intro i _
    simp only [Function.comp_def,List.getElem?_cons_succ]
    congr 1
    omega

theorem encodeCNF_append_local (F G : CNF) : encodeCNF (F++G) = encodeCNF F ++ encodeCNF G := by
  simp [encodeCNF,List.flatMap_append]

theorem run_from (F : CNF) (hF : IsKCNF 4 F) (n : ℕ) (o : Word) (k : ℕ)
    (hk : F.length ≤ k) :
    step^[k] (pack (encodeCNF F) n.bits o) =
      pack [] (n+F.length).bits (o ++ encodeCNF (splitFrom n F)) := by
  induction F generalizing n o k with
  | nil =>
    have h : step (pack [] n.bits o) = pack [] n.bits o := by
      simp [step,rest,pack,sel,unpairB_pairB]
    simpa [encodeCNF,splitFrom] using Function.iterate_fixed h k
  | cons cl F ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [Function.iterate_succ_apply,show encodeCNF (cl::F) = encodeClause cl ++ encodeCNF F by rfl,
        step_close cl (hF cl (List.mem_cons_self ..)),
        ih (fun c hc => hF c (List.mem_cons_of_mem _ hc)) (n+1) _ k (by simpa using hk)]
      simp only [splitFrom,List.length_cons,encodeCNF_append_local,
        List.append_assoc]
      congr 2
      omega

theorem encode_length_lower (F : CNF) : F.length ≤ (encodeCNF F).length := by
  induction F with
  | nil => simp
  | cons cl F ih =>
    simp only [encodeCNF, List.flatMap_cons,encodeClause,List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem run_enc (F : CNF) (hF : IsKCNF 4 F) :
    run (encodeCNF F) = encodeCNF (splitCNF F) := by
  unfold run
  change result (step^[(encodeCNF F).length] (pack (encodeCNF F) (0:ℕ).bits [])) = _
  rw [run_from F hF 0 [] _ (encode_length_lower F)]
  simp [result, pack,unpairB_pairB,splitFrom_range,splitCNF]

end PEqualNP.Outside.CNFWidth

open PEqualNP.Library PEqualNP.Search

theorem PEqualNP.Outside.MeasuredClauseSplit :
    ∃ F : List Bool → List Bool,
      ComputableInPolyTime (fun s : List Bool => s) (fun s : List Bool => s) F ∧
      ∀ φ : CNF, IsKCNF 4 φ →
        ∃ ψ : CNF, F (encodeCNF φ) = encodeCNF ψ ∧ IsKCNF 3 ψ ∧
          Nonempty (
            {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                then a ⟨i,h⟩ else false) φ = true} ≃
            {b : {i : ℕ // i ∈ ψ.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ ψ.flatMap (List.map Prod.fst)
                then b ⟨i,h⟩ else false) ψ = true}) := by
  open PEqualNP.Outside.CNFWidth in
  exact ⟨run,run_cpt,fun φ hφ => ⟨splitCNF φ,run_enc φ hφ,split_width φ hφ,⟨splitEquiv φ⟩⟩⟩
