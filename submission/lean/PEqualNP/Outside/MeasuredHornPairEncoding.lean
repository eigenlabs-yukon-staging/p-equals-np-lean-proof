import PEqualNP.Outside.RenamableHornPairConstraints
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private theorem encode_cons (l : Literal) (c : Clause) :
    encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]

private theorem cnf_app (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF,List.flatMap_append]

private theorem first_bit (w : List Bool) : hd w ≠ [] ↔ w.headD false = true := by
  cases w with
  | nil => simp [hd]
  | cons b w => cases b <;> simp [hd]

private theorem drop_nil (n : ℕ) : dropI^[n] ([] : List Bool) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,show dropI [] = [] by rfl,ih]

private theorem drop_encoded (c : Clause) (i : ℕ) :
    dropI^[i] (encodeClause c) = if i ≤ c.length then encodeClause (c.drop i) else [] := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply]
      cases c with
      | nil => exact drop_nil i
      | cons l c =>
          rw [encode_cons,dropI_lit,ih]
          simp

private theorem range_repeat_empty (n : ℕ) (f : ℕ → List Bool) (hf : ∀ i, f i = []) :
    (List.range n).flatMap f = [] := by
  rw [List.flatMap_eq_nil_iff]
  exact fun i _ => hf i

private def unitPair (lit word : List Bool) : List Bool :=
  if word.headD false then lit ++ headI word ++ [false,false] else []

private theorem inner_cons (l m : Literal) (c : Clause) :
    unitPair (encodeLiteral l) (encodeClause (m :: c)) = encodeClause [l,m] := by
  rw [unitPair,encode_cons,headI_lit]
  have hm : (encodeLiteral m ++ encodeClause c).headD false = true := rfl
  rw [ite_eq_left hm]
  simp [encodeClause,List.append_assoc]

private theorem inner_range (l : Literal) (c : Clause) (n : ℕ) (hn : c.length ≤ n) :
    (List.range n).flatMap (fun i => unitPair (encodeLiteral l) (dropI^[i] (encodeClause c))) =
      encodeCNF (c.map (fun m => [l,m])) := by
  induction c generalizing n with
  | nil =>
      have h (i : ℕ) : unitPair (encodeLiteral l) (dropI^[i] (encodeClause [])) = [] := by
        rw [drop_encoded]
        cases i <;> rfl
      rw [range_repeat_empty _ _ h]
      rfl
  | cons m c ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hc : c.length ≤ n := by simpa using hn
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have he (i : ℕ) :
              dropI^[i+1] (encodeClause (m :: c)) = dropI^[i] (encodeClause c) := by
            rw [Function.iterate_succ_apply,encode_cons,dropI_lit]
          simp only [Function.comp_apply,he,Function.iterate_zero_apply,inner_cons]
          rw [ih n hc]
          rfl

private theorem encode_count (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      rw [encode_cons,List.length_append,List.length_cons]
      have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega

private theorem measured_pairs_with :
    ∃ pairWith : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) pairWith ∧
      ∀ (l : Literal) (c : Clause),
        pairWith (encodeLiteral l,encodeClause c) = encodeCNF (c.map (fun m => [l,m])) := by
  let picked := fun s => dropI^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) picked :=
    cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let lit := fun s => (unpairB (unpairB s).2).1
  have hl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lit :=
    cpt_unpairB1_1 cpt_unpairB2
  let f := fun s => unitPair (lit s) (picked s)
  have hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f := by
    refine cptE (cpt_sel (cpt_hd1 hp) (cpt_const [])
      (cpt_app2 hl (cpt_app2 (cpt_comp hp cpt_headI) (cpt_const [false,false])))) (fun s => ?_)
    unfold f unitPair
    cases picked s with
    | nil => rfl
    | cons b r => cases b <;> simp [sel,hd,List.append_assoc]
  let raw := fun s => (List.range (unpairB s).2.length).flatMap
    (fun i => f (pairB (un i) s))
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_flatMapRange hf cpt_unpairB2 cpt_id
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp cpt_pairB hr,fun l c => ?_⟩
  simp only [raw,f,lit,picked,unpairB_pairB,un_length]
  exact inner_range l c _ (encode_count c)

private theorem outer_range (pairWith : List Bool × List Bool → List Bool)
    (hs : ∀ (l : Literal) (c : Clause),
      pairWith (encodeLiteral l,encodeClause c) = encodeCNF (c.map (fun m => [l,m])))
    (c : Clause) (n : ℕ) (hn : c.length ≤ n) :
    (List.range n).flatMap (fun i =>
      let rem := dropI^[i] (encodeClause c)
      if rem.headD false then pairWith (headI rem,dropI rem) else []) = encodeCNF (hornPairClauses c) := by
  induction c generalizing n with
  | nil =>
      have he (i : ℕ) : (if (dropI^[i] (encodeClause [])).headD false then
          pairWith (headI (dropI^[i] (encodeClause [])),dropI (dropI^[i] (encodeClause []))) else []) = [] := by
        rw [drop_encoded]
        cases i <;> rfl
      rw [range_repeat_empty _ _ he]
      rfl
  | cons l c ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hc : c.length ≤ n := by simpa using hn
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have he (i : ℕ) :
              dropI^[i+1] (encodeClause (l :: c)) = dropI^[i] (encodeClause c) := by
            rw [Function.iterate_succ_apply,encode_cons,dropI_lit]
          simp only [Function.comp_apply,he,Function.iterate_zero_apply]
          have hb : (encodeClause (l :: c)).headD false = true := rfl
          simp only [hb,ite_true]
          rw [encode_cons,headI_lit,dropI_lit,hs,ih n hc]
          rw [hornPairClauses,cnf_app]

private theorem measured_clause_pairs :
    ∃ expand : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) expand ∧
      ∀ c : Clause, expand (encodeClause c) = encodeCNF (hornPairClauses c) := by
  obtain ⟨withLit,hw,hs⟩ := measured_pairs_with
  let remaining := fun s => dropI^[(unpairB s).1.length] (unpairB s).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) remaining :=
    cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2
  let branch := fun s => if (remaining s).headD false then
    withLit (headI (remaining s),dropI (remaining s)) else []
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch := by
    have hpair := cpt_pair (cpt_comp hr cpt_headI) (cpt_comp hr cpt_dropI)
    have hh := cpt_comp hpair hw
    refine cptE (cpt_sel (cpt_hd1 hr) (cpt_const []) hh) (fun s => ?_)
    unfold branch
    cases remaining s with
    | nil => rfl
    | cons b r => cases b <;> rfl
  let expand := fun s => (List.range s.length).flatMap (fun i => branch (pairB (un i) s))
  have he : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) expand :=
    cpt_flatMapRange hb cpt_id cpt_id
  refine ⟨expand,he,fun c => ?_⟩
  simp only [expand,branch,remaining,unpairB_pairB,un_length]
  exact outer_range withLit hs c _ (encode_count c)

private theorem formula_range (split : List Bool → List Bool × List Bool)
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hempty : (split []).2 = [])
    (expand : List Bool → List Bool)
    (he : ∀ c : Clause, expand (encodeClause c) = encodeCNF (hornPairClauses c))
    (φ : CNF) (n : ℕ) (hn : φ.length ≤ n) :
    (List.range n).flatMap (fun i =>
      let r := (fun s => (split s).2)^[i] (encodeCNF φ)
      if r = [] then [] else expand (split r).1) = encodeCNF (hornRenamingConstraints φ) := by
  induction φ generalizing n with
  | nil =>
      have hz (i : ℕ) : (fun s => (split s).2)^[i] ([] : List Bool) = [] := by
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply,hempty,ih]
      have hh (i : ℕ) : (if (fun s => (split s).2)^[i] (encodeCNF []) = [] then []
          else expand (split ((fun s => (split s).2)^[i] (encodeCNF []))).1) = [] := by
        have e : encodeCNF [] = [] := rfl
        rw [e,hz]
        rfl
      rw [range_repeat_empty _ _ hh]
      rfl
  | cons c φ ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have ht : φ.length ≤ n := by simpa using hn
          have henc : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
          have hne : encodeCNF (c :: φ) ≠ [] := by rw [henc]; simp [encodeClause]
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have hnext (i : ℕ) :
              (fun s => (split s).2)^[i+1] (encodeCNF (c :: φ)) =
                (fun s => (split s).2)^[i] (encodeCNF φ) := by
            rw [Function.iterate_succ_apply,henc]
            simp only [hs]
          simp only [hnext,Function.iterate_zero_apply]
          change (if encodeCNF (c :: φ) = [] then [] else expand (split (encodeCNF (c :: φ))).1) ++
            (List.range n).flatMap (fun i =>
              let r := (fun s => (split s).2)^[i] (encodeCNF φ)
              if r = [] then [] else expand (split r).1) = _
          rw [ite_eq_right hne,henc,hs,he,ih n ht]
          change encodeCNF (hornPairClauses c) ++ encodeCNF (hornRenamingConstraints φ) =
            encodeCNF (hornPairClauses c ++ hornRenamingConstraints φ)
          rw [cnf_app]

private theorem formula_count (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      change φ.length+1 ≤ (encodeClause c ++ encodeCNF φ).length
      simp only [encodeClause,List.length_append,List.length_cons,List.length_nil]
      omega

theorem measuredHornPairEncoding_semantics :
    ∃ make : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) make ∧
      ∀ φ : CNF, make (encodeCNF φ) = encodeCNF (hornRenamingConstraints φ) := by
  obtain ⟨split,hs,hjoin,hspec⟩ := measuredFirstClause_reassembles
  obtain ⟨expand,he,hespec⟩ := measured_clause_pairs
  let tail := fun s => (split s).2
  have ht : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) tail :=
    cpt_comp hs cpt_snd
  have hlen (s : List Bool) : (tail s).length ≤ s.length := by
    have h := congrArg List.length (hjoin s)
    simp only [List.length_append] at h
    dsimp only [tail]
    omega
  let cursor := fun s => tail^[(unpairB s).1.length] (unpairB s).2
  have hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cursor :=
    cpt_iterLen ht hlen cpt_unpairB1 cpt_unpairB2
  let branch := fun s => if cursor s = [] then [] else expand (split (cursor s)).1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch :=
    cpt_sel hc (cpt_const []) (cpt_comp (cpt_comp (cpt_comp hc hs) cpt_fst) he)
  let make := fun s => (List.range s.length).flatMap (fun i => branch (pairB (un i) s))
  have hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) make :=
    cpt_flatMapRange hb cpt_id cpt_id
  refine ⟨make,hm,fun φ => ?_⟩
  simp only [make,branch,cursor,tail,unpairB_pairB,un_length]
  have hempty : (split []).2 = [] := by
    have he := hjoin []
    exact (List.append_eq_nil_iff.mp he).2
  exact formula_range split hspec hempty expand hespec φ _ (formula_count φ)

/-- Construct the 2-CNF Horn-renaming constraints in measured polynomial time. -/
theorem MeasuredHornPairEncoding :
    ∃ make : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) make ∧
      ∀ φ : CNF, ∃ F : CNF, IsKCNF 2 F ∧ make (encodeCNF φ) = encodeCNF F ∧
        ∀ flip : Assignment, CNF.eval flip F = true ↔
          ∀ c ∈ φ, ((c.map (fun l => (l.1, xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1 := by
  obtain ⟨make,hm,hs⟩ := measuredHornPairEncoding_semantics
  refine ⟨make,hm,fun φ => ⟨hornRenamingConstraints φ,pair_constraints_width φ,hs φ,fun flip => ?_⟩⟩
  rw [pair_constraints_truth]
  constructor
  · intro h c hc
    exact h _ (List.mem_map_of_mem hc)
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact h d hd

end PEqualNP.Outside
