import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private def addSmall (code rest small groups : List Bool) : List Bool :=
  pairB rest (pairB (code ++ small) groups)

private def addTriple (a b c rest small groups : List Bool) : List Bool :=
  let unit := fun x => x ++ [false,false]
  pairB rest (pairB small (pairB (pairB (unit a) (pairB (unit b) (unit c))) groups))

private def packStep (s : List Bool) : List Bool :=
  let r₀ := (unpairB s).1
  let r₁ := dropI r₀
  let r₂ := dropI r₁
  let r₃ := dropI r₂
  let r₄ := dropI r₃
  let small := (unpairB (unpairB s).2).1
  let groups := (unpairB (unpairB s).2).2
  let a := headI r₀
  let b := headI r₁
  let c := headI r₂
  if r₀ = [] then s
  else if isEnd r₀ then addSmall [false,false] r₁ small groups
  else if isEnd r₁ then addSmall (a ++ [false,false]) r₂ small groups
  else if isEnd r₂ then addSmall (a ++ b ++ [false,false]) r₃ small groups
  else addTriple a b c r₄ small groups

private theorem cpt_packStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) packStep := by
  have hr0 := cpt_unpairB1
  have hr1 := cpt_comp hr0 cpt_dropI
  have hr2 := cpt_comp hr1 cpt_dropI
  have hr3 := cpt_comp hr2 cpt_dropI
  have hr4 := cpt_comp hr3 cpt_dropI
  have hsmall := cpt_unpairB1_1 cpt_unpairB2
  have hgroups := cpt_unpairB2_1 cpt_unpairB2
  have ha := cpt_comp hr0 cpt_headI
  have hb := cpt_comp hr1 cpt_headI
  have hc := cpt_comp hr2 cpt_headI
  have hend := cpt_const [false,false]
  have hzero := cpt_pairB2 hr1 (cpt_pairB2 (cpt_app2 hend hsmall) hgroups)
  have hone := cpt_pairB2 hr2 (cpt_pairB2 (cpt_app2 (cpt_app2 ha hend) hsmall) hgroups)
  have htwo := cpt_pairB2 hr3 (cpt_pairB2 (cpt_app2 (cpt_app2 (cpt_app2 ha hb) hend) hsmall) hgroups)
  have hthree := cpt_pairB2 hr4 (cpt_pairB2 hsmall
    (cpt_pairB2 (cpt_pairB2 (cpt_app2 ha hend)
      (cpt_pairB2 (cpt_app2 hb hend) (cpt_app2 hc hend))) hgroups))
  have hsel := cpt_sel hr0 cpt_id (cpt_sel (cpt_comp hr0 cpt_isEndF)
    (cpt_sel (cpt_comp hr1 cpt_isEndF) (cpt_sel (cpt_comp hr2 cpt_isEndF) hthree htwo) hone) hzero)
  refine cptE hsel (fun s => ?_)
  dsimp only [packStep, addSmall, addTriple, sel]
  split
  · rfl
  · cases isEnd (unpairB s).1 <;>
      cases isEnd (dropI (unpairB s).1) <;>
      cases isEnd (dropI (dropI (unpairB s).1)) <;> rfl

private theorem firstLen_packStep (s : List Bool) :
    (unpairB (packStep s)).1.length ≤ (unpairB s).1.length := by
  dsimp only [packStep]
  split
  · rfl
  · split
    · exact (by simpa [addSmall, unpairB_pairB] using dropI_length (unpairB s).1)
    · split
      · exact (by simpa [addSmall, unpairB_pairB] using
          (dropI_length (dropI (unpairB s).1)).trans (dropI_length (unpairB s).1))
      · split
        · simp only [addSmall, unpairB_pairB]
          exact (dropI_length _).trans ((dropI_length _).trans (dropI_length _))
        · simp only [addTriple, unpairB_pairB]
          exact (dropI_length _).trans ((dropI_length _).trans ((dropI_length _).trans (dropI_length _)))

private theorem headI_length (s : List Bool) : (headI s).length ≤ s.length := by
  have h := congrArg List.length (headI_dropI s)
  simp only [List.length_append] at h
  omega

private theorem packStep_length (s : List Bool) :
    (packStep s).length ≤ s.length + (20 * (unpairB s).1.length + 30) := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have hdrop1 := dropI_length (unpairB s).1
  have hdrop2 := dropI_length (dropI (unpairB s).1)
  have hdrop3 := dropI_length (dropI (dropI (unpairB s).1))
  have hdrop4 := dropI_length (dropI (dropI (dropI (unpairB s).1)))
  have ha := headI_length (unpairB s).1
  have hb := headI_length (dropI (unpairB s).1)
  have hc := headI_length (dropI (dropI (unpairB s).1))
  dsimp only [packStep]
  split <;> try omega
  split
  · simp only [addSmall, pairB_length, List.length_append, List.length_cons, List.length_nil]
    omega
  · split
    · simp only [addSmall, pairB_length, List.length_append, List.length_cons, List.length_nil]
      omega
    · split
      · simp only [addSmall, pairB_length, List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [addTriple, pairB_length, List.length_append, List.length_cons, List.length_nil]
        omega

private theorem isEnd_delim (r : List Bool) : isEnd ([false,false] ++ r) = true := rfl

private theorem dropI_delim (r : List Bool) : dropI ([false,false] ++ r) = r := rfl

private theorem literal_nonempty (l : Literal) (r : List Bool) : encodeLiteral l ++ r ≠ [] := by
  simp [encodeLiteral]

private theorem packStep_small (c : Clause) (tail small groups : List Bool) (hc : c.length ≤ 2) :
    packStep (pairB (encodeClause c ++ tail) (pairB small groups)) =
      pairB tail (pairB (encodeClause c ++ small) groups) := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [packStep, addSmall, unpairB_pairB, encodeClause, isEnd, dropI]
  · simp only [packStep, addSmall, unpairB_pairB, encodeClause, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_assoc, literal_nonempty, dropI_lit,
      headI_lit, isEnd_lit, isEnd_delim, dropI_delim, Bool.false_eq_true, ite_false, ite_true]
  · simp only [packStep, addSmall, unpairB_pairB, encodeClause, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_assoc, literal_nonempty, dropI_lit,
      headI_lit, isEnd_lit, isEnd_delim, dropI_delim, Bool.false_eq_true, ite_false, ite_true]
  · simp at hc

private abbrev Triple := Literal × Literal × Literal

private def triples (φ : CNF) : List Triple :=
  φ.filterMap (fun c => if c.length = 3 then some (c.getD 0 (0,false),
          c.getD 1 (0,false), c.getD 2 (0,false)) else none)

private def packTriples (groups : List Triple) : List Bool :=
  groups.foldr (fun group rest =>
    pairB (pairB (encodeClause [group.1]) (pairB (encodeClause [group.2.1]) (encodeClause [group.2.2]))) rest) []

private theorem packStep_triple (a b c : Literal) (tail small groups : List Bool) :
    packStep (pairB (encodeClause [a,b,c] ++ tail) (pairB small groups)) =
      pairB tail (pairB small
        (pairB (pairB (encodeClause [a]) (pairB (encodeClause [b]) (encodeClause [c]))) groups)) := by
  simp only [packStep, addTriple, unpairB_pairB, encodeClause, List.flatMap_cons,
    List.flatMap_nil, List.nil_append, List.append_assoc, literal_nonempty, dropI_lit,
    headI_lit, isEnd_lit, dropI_delim, Bool.false_eq_true, ite_false]

private theorem run_pack (φ : CNF) (hφ : IsKCNF 3 φ) (small groups : List Bool) (n : ℕ)
    (hn : φ.length ≤ n) :
    packStep^[n] (pairB (encodeCNF φ) (pairB small groups)) =
      pairB [] (pairB (encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse) ++ small)
        (((triples φ).reverse).foldr (fun (a,b,c) rest =>
          pairB (pairB (encodeClause [a]) (pairB (encodeClause [b]) (encodeClause [c]))) rest) groups)) := by
  induction n generalizing φ small groups with
  | zero =>
      have h : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have e : packStep (pairB (encodeCNF []) (pairB small groups)) =
              pairB (encodeCNF []) (pairB small groups) := by simp [packStep, unpairB_pairB, encodeCNF]
          rw [e, ih [] hφ _ _ (by simp)]
      | cons c φ =>
          have ht : IsKCNF 3 φ := fun g hg => hφ g (List.mem_cons_of_mem _ hg)
          have hc := hφ c List.mem_cons_self
          have htail : φ.length ≤ n := by simpa using hn
          change packStep^[n] (packStep (pairB (encodeClause c ++ encodeCNF φ) (pairB small groups))) = _
          rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
          · rw [packStep_small _ _ _ _ (by simp), ih _ ht _ _ htail]
            simp [triples, encodeCNF, List.flatMap_append, List.append_assoc]
          · rw [packStep_small _ _ _ _ (by simp), ih _ ht _ _ htail]
            simp [triples, encodeCNF, List.flatMap_append, List.append_assoc]
          · rw [packStep_small _ _ _ _ (by simp), ih _ ht _ _ htail]
            simp [triples, encodeCNF, List.flatMap_append, List.append_assoc]
          · rw [packStep_triple, ih _ ht _ _ htail]
            simp [triples]
          · simp at hc
            omega

private theorem cnf_count_le (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
      change φ.length + 1 ≤ (encodeClause c ++ encodeCNF φ).length
      simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
      omega

/-- Measured partition of a reference 3-CNF into a 2-CNF base and reversed packed
triples of unit-clause alternatives. -/
theorem CNFThreeClausePacking :
    ∃ pack : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pack ∧
      ∀ φ : CNF, IsKCNF 3 φ →
        let small := encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse)
        let groups := (φ.filterMap (fun c => if c.length = 3 then some (c.getD 0 (0,false),
          c.getD 1 (0,false), c.getD 2 (0,false)) else none)).reverse
        let packed := groups.foldr (fun group rest =>
          let a := encodeClause [group.1]
          let b := encodeClause [group.2.1]
          let c := encodeClause [group.2.2]
          let bc := List.replicate b.length true ++ false :: (b ++ c)
          let abc := List.replicate a.length true ++ false :: (a ++ bc)
          List.replicate abc.length true ++ false :: (abc ++ rest)) []
        pack (encodeCNF φ) = List.replicate small.length true ++ false :: (small ++ packed) := by
  let measure := fun s => 20 * (unpairB s).1.length + 30
  have hdec (s : List Bool) : measure (packStep s) ≤ measure s := by
    dsimp only [measure]
    have h := firstLen_packStep s
    omega
  have hbound (s : List Bool) : measure s ≤ 30 * s.length + 30 := by
    dsimp only [measure]
    have h := unpairB_length s
    omega
  let start := fun s => pairB s (pairB [] [])
  let out := fun s => (unpairB (packStep^[s.length] (start s))).2
  have hstart := cpt_pairB2 cpt_id (cpt_const (pairB [] []))
  have hout : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) out :=
    cpt_unpairB2_1 (cpt_iterMeasure cpt_packStep measure 30 hdec packStep_length hbound cpt_id hstart)
  refine ⟨out, hout, fun φ hφ => ?_⟩
  change out (encodeCNF φ) = pairB (encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse))
    (packTriples (triples φ).reverse)
  simp only [out, start, run_pack φ hφ [] [] _ (cnf_count_le φ), List.append_nil, unpairB_pairB]
  rfl

end PEqualNP.Outside
