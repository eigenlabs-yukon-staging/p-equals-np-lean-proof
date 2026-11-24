import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Verifier" => List Bool × List Bool → Bool

private def searchStep (v : Verifier) (s : List Bool) : List Bool :=
  let (input, rest) := unpairB s
  let (candidate, flags) := unpairB rest
  pairB input (pairB (succB candidate) (flags ++ bflag (v (input, candidate))))

private theorem searchStep_size (v : Verifier) (s : List Bool) :
    (searchStep v s).length ≤ s.length + 5 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have hc := bf_succB_length (unpairB (unpairB s).2).1
  have hf := bf_bflag_length (v ((unpairB s).1, (unpairB (unpairB s).2).1))
  simp only [searchStep, pairB_length, List.length_append]
  omega

private theorem searchStep_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    CPT (searchStep v) := by
  have hInput : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hRest : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hCandidate := cpt_unpairB1_1 hRest
  have hFlags := cpt_unpairB2_1 hRest
  have hTest := cpt_comp (cpt_pair hInput hCandidate) hv
  have hBit := bf_cptl (cpt_bitFlag hTest) (fun _ => rfl)
  have hNext := cpt_comp hCandidate bf_cpt_succB
  exact bf_cptl (cpt_pairB2 hInput (cpt_pairB2 hNext (cpt_app2 hFlags hBit)))
    (fun _ => rfl)

private theorem searchStep_packed (v : Verifier) (x c fl : List Bool) :
    searchStep v (pairB x (pairB c fl)) = pairB x (pairB (succB c) (fl ++ bflag (v (x,c)))) := by
  simp [searchStep, unpairB_pairB]

private theorem search_iter (v : Verifier) (x : List Bool) (k : Nat) :
    ∀ c fl : List Bool, ∃ fl' : List Bool,
      (searchStep v)^[k] (pairB x (pairB c fl)) = pairB x (pairB (succB^[k] c) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, v (x, succB^[j] c) = false) := by
  induction k with
  | zero => intro c fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro c fl
    obtain ⟨fl', hstate, hflag⟩ := ih (succB c) (fl ++ bflag (v (x, c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, searchStep_packed, hstate, Function.iterate_succ_apply]
    · rw [hflag, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

private def search (v : Verifier) (x : List Bool) (k : Nat) : List Bool :=
  (unpairB (unpairB ((searchStep v)^[k] (pairB x (pairB [] [])))).2).2

private theorem search_empty (v : Verifier) (x : List Bool) (k : Nat) :
    search v x k = [] ↔ ∀ j < k, v (x, cand j) = false := by
  obtain ⟨flags, hstate, hflag⟩ := search_iter v x k [] []
  rw [search, hstate]
  simpa [unpairB_pairB, cand] using hflag

private theorem search_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat) :
    CPT (fun x => search v x (p.eval x.length)) :=
  bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1
    (cpt_iterGrow (searchStep_polyTime hv) 5 (searchStep_size v) (L055 p)
      (cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) (cpt_const []))))))
    (fun x => by simp [search])

/-- A single deterministic polynomial-time machine works on every input once the
search coverage polynomial is fixed. Only one short witness per yes-input is needed. -/
theorem PolynomialWitnessSearch (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (covers : ∀ x : List Bool, (∃ w : List Bool, (x, w) ∈ R) →
      ∃ w : List Bool, (x, w) ∈ R ∧ 2 ^ (w.length + 1) ≤ p.eval x.length + 1) :
    ({x : List Bool | ∃ w : List Bool, (x, w) ∈ R} : Language Bool) ∈ P := by
  obtain ⟨v, spec, hv⟩ := hR
  let decideSearch := fun x : List Bool => !(search v x (p.eval x.length)).isEmpty
  have hdecide : ComputableInPolyTime (fun x => x) Computability.encodeBool decideSearch :=
    cpt_comp (g := fun l => !l.isEmpty) (search_polyTime hv p) bf_cpt_neL
  refine ⟨decideSearch, ?_, hdecide⟩
  intro x
  change (∃ w : List Bool, (x, w) ∈ R) ↔ _
  simp only [decideSearch, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  simp only [ne_eq, search_empty]
  constructor
  · rintro hx hempty
    obtain ⟨w, hw, hlen⟩ := covers x hx
    have hidx := idx_bound w
    have hcheck := hempty (idx w) (by omega)
    rw [cand_idx, (spec (x, w)).mp hw] at hcheck
    contradiction
  · intro h
    by_contra hno
    apply h
    intro j _
    cases ha : v (x, cand j)
    · rfl
    · exact False.elim (hno ⟨cand j, (spec (x, cand j)).mpr ha⟩)

end PEqualNP.Outside
