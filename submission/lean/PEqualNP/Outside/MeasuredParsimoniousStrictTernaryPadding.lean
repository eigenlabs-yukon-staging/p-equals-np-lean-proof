import PEqualNP.Outside.UniqueTernaryPaddingEmit
import PEqualNP.Outside.ParsimoniousStrictTernaryPadding

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.TernaryGadget (slots plusBits plusBits_cpt plusBits_len plusBits_enc)
open PEqualNP.Outside.SatCodePrimitives (cptl cpt_dropI)
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.CNFWidth (Word raw advance raw_cpt advance_cpt rest index result pack pass
  pass_decreases advance_length measure_bounds raw_lit advance_lit raw_close advance_close
  encodeCNF_append_local encode_length_lower)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def scanBlock (n r : Word) : Word :=
  emitRaw n (raw r) (raw (advance r)) (raw (advance (advance r)))

def step (s : Word) : Word :=
  let r := rest s
  let n := index s
  let emitted := scanBlock n r
  sel r s (pack (pass r) (plusBits 21 n) (result s ++ emitted))

set_option maxHeartbeats 1600000 in
theorem step_cpt : CPT step := by
  have hr := cpt_unpairB1
  have h1 := cpt_comp hr advance_cpt
  have h2 := cpt_comp h1 advance_cpt
  have h3 := cpt_comp h2 advance_cpt
  have h4 := cpt_comp h3 advance_cpt
  have hn := cpt_unpairB1_1 cpt_unpairB2
  have ho := cpt_unpairB2_1 cpt_unpairB2
  have hb := emitRaw_cpt hn (cpt_comp hr raw_cpt) (cpt_comp h1 raw_cpt)
    (cpt_comp h2 raw_cpt)
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 (cpt_comp h4 cpt_dropI)
    (cpt_pairB2 (cpt_comp hn (plusBits_cpt 21)) (cpt_app2 ho hb))))
    (fun _ => rfl)

def growth (K : ℕ) (s : Word) := K*(21*(rest s).length+(index s).length+1)+32

theorem growth_invariant (K : ℕ) (s : Word) : growth K (step s) ≤ growth K s := by
  by_cases hr : rest s = []
  · simp [step,sel,hr]
  · have hp := pass_decreases hr
    have hn := plusBits_len 21 (index s)
    rw [step,sel,ite_eq_right hr]
    simp only [growth,pack,rest,index,unpairB_pairB] at *
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega

theorem scanBlock_len : ∃ K, ∀ n r : Word,
    (scanBlock n r).length ≤ r.length + K*(n.length+1) := by
  obtain ⟨K,hK⟩ := emitRaw_len
  refine ⟨K,fun n r => ?_⟩
  have h := hK n (raw r) (raw (advance r)) (raw (advance (advance r)))
  have h1 := advance_length r
  have h2 := advance_length (advance r)
  have h3 := advance_length (advance (advance r))
  unfold scanBlock
  omega

theorem growth_length :
    ∃ K, ∀ s : Word, (step s).length ≤ s.length + growth K s := by
  obtain ⟨k,hk⟩ := scanBlock_len
  refine ⟨k+1,fun s => ?_⟩
  by_cases hr : rest s = []
  · simp [step,sel,hr]
  · have hm := measure_bounds s
    have hp := pass_decreases hr
    have hn := plusBits_len 21 (index s)
    have hb := hk (index s) (rest s)
    have hg := Nat.mul_le_mul_left k (show (index s).length+1 ≤
      21*(rest s).length+(index s).length+1 by omega)
    rw [step,sel,ite_eq_right hr]
    simp only [pack,pairB_length,List.length_append,growth,Nat.add_mul,Nat.one_mul]
    omega

def run (r : Word) : Word := result (step^[r.length] (pack r [] []))

theorem run_cpt : CPT run := by
  obtain ⟨m⟩ := step_cpt
  obtain ⟨K,hK⟩ := growth_length
  have iter := Iter.iter_polyTime_measure step m (growth K) (32+K+21*K)
    (growth_invariant K) hK (fun s => by
      have hm := measure_bounds s
      unfold growth
      rw [Nat.mul_add,Nat.mul_one]
      have hmain : 21*(rest s).length+(index s).length ≤ 21*s.length := by omega
      have hb := Nat.mul_le_mul_left K hmain
      rw [← Nat.mul_assoc, Nat.mul_comm K 21] at hb
      calc
        K * (21 * (rest s).length + (index s).length) + K + 32 ≤ 21*K*s.length + K + 32 := by omega
        _ ≤ (32+K+21*K)*(s.length+1) := by
          simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
          omega)
  have hpack : CPT (fun r => pack r [] []) :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) (cpt_const []))
  have hout : CPT result := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pair hpack cpt_id) iter) hout) (fun _ => rfl)


theorem scanBlock_close (cl : Clause) (h : cl.length ≤ 3) (j : ℕ) (r : Word) :
    scanBlock (21*j).bits (encodeClause cl ++ r) =
      encodeCNF (block j cl) := by
  rw [← emit_slots cl j h]
  rcases cl with _ | ⟨a,_ | ⟨b,_ | ⟨d,cs⟩⟩⟩
  · rfl
  · simp [scanBlock,slots,encodeClause,List.flatMap_cons,List.append_assoc,
      advance_lit,advance_close,raw_lit,raw_close]
  · simp [scanBlock,slots,encodeClause,List.flatMap_cons,List.append_assoc,
      advance_lit,advance_close,raw_lit,raw_close]
  · have hs : cs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
    subst cs
    simp [scanBlock,slots,encodeClause,List.flatMap_cons,List.append_assoc,
      advance_lit,advance_close,raw_lit,raw_close]

theorem pass_close (cl : Clause) (h : cl.length ≤ 3) (r : Word) :
    pass (encodeClause cl ++ r) = r := by
  match cl with
  | [] | [_] | [_,_] | [_,_,_] =>
    simp [pass,encodeClause,List.flatMap_cons,List.append_assoc,advance_lit,advance_close,dropI]
  | _::_::_::_::_ =>
    simp only [List.length_cons] at h
    omega

theorem step_close (cl : Clause) (h : cl.length ≤ 3) (j : ℕ) (r o : Word) :
    step (pack (encodeClause cl ++ r) (21*j).bits o) =
      pack r (21*(j+1)).bits (o ++ encodeCNF (block j cl)) := by
  have hnon : encodeClause cl ++ r ≠ [] := by simp [encodeClause]
  have hnext : 21*j+21 = 21*(j+1) := by omega
  simp only [step,rest,index,result,pack,unpairB_pairB,sel,ite_eq_right hnon,pass_close cl h,
    scanBlock_close cl h,plusBits_enc,hnext]

theorem run_from (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) (o : Word) (k : ℕ)
    (hk : F.length ≤ k) :
    step^[k] (pack (encodeCNF F) (21*j).bits o) =
      pack [] (21*(j+F.length)).bits (o ++ encodeCNF (padFrom j F)) := by
  induction F generalizing j o k with
  | nil =>
    have h : step (pack [] (21*j).bits o) = pack [] (21*j).bits o := by
      simp [step,rest,pack,sel,unpairB_pairB]
    simpa [encodeCNF,padFrom] using Function.iterate_fixed h k
  | cons cl F ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hTail : IsKCNF 3 F := fun c hc => hF c (List.mem_cons_of_mem _ hc)
      have hk' : F.length ≤ k := by simpa using hk
      rw [Function.iterate_succ_apply,show encodeCNF (cl::F) = encodeClause cl ++ encodeCNF F by rfl,
        step_close cl (hF cl (List.mem_cons_self ..)),ih hTail (j+1) _ k hk']
      simp only [List.length_cons,padFrom,encodeCNF_append_local,List.append_assoc]
      rw [show j+1+F.length = j+(F.length+1) by omega]

set_option maxHeartbeats 1400000 in
theorem run_enc (F : CNF) (hF : IsKCNF 3 F) :
    run (encodeCNF F) = encodeCNF (padFrom 0 F) := by
  unfold run
  change result (step^[(encodeCNF F).length] (pack (encodeCNF F) (21*0).bits [])) = _
  rw [run_from F hF 0 [] _ (encode_length_lower F)]
  simp only [result,pack,unpairB_pairB,List.nil_append]

end PEqualNP.Outside.UniqueTernaryGadget

open PEqualNP.Library PEqualNP.Search

theorem PEqualNP.Outside.MeasuredParsimoniousStrictTernaryPadding :
    ∃ g : List Bool → List Bool,
      ComputableInPolyTime (fun s : List Bool => s) (fun s : List Bool => s) g ∧
      ∀ F : CNF, IsKCNF 3 F →
        (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 5) →
        ∃ G : CNF, g (encodeCNF F) = encodeCNF G ∧
          (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
          (∀ v, (G.flatMap (List.map Prod.fst)).count v ≤ 5) ∧
          Nonempty (
            {a : {i : ℕ // i ∈ F.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ F.flatMap (List.map Prod.fst) then a ⟨i,h⟩ else false) F = true} ≃
            {a : {i : ℕ // i ∈ G.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ G.flatMap (List.map Prod.fst) then a ⟨i,h⟩ else false) G = true}) := by
  open PEqualNP.Outside.UniqueTernaryGadget in
  exact ⟨run,run_cpt,fun F hW hD =>
    ⟨padFrom 0 F,run_enc F hW,pad_shape F hW 0,pad_degree F 0 hD,⟨modelEquiv F hW 0⟩⟩⟩
