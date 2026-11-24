import PEqualNP.Outside.FiniteQuantifiedWordCollapse
import PEqualNP.Outside.ShortestLexWitnessSearch

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside (FiniteQuantifiedWordCollapse ShortestLexWitnessSearch)

private abbrev Word := List Bool

private def continueGame (H : Language Bool) (tail : List (Bool × Polynomial ℕ)) (x : Word) : Prop :=
  tail.foldr (fun q next y =>
    if q.1 then ∀ w : Word, w.length ≤ q.2.eval y.length → next (pairB y w)
    else ∃ w : Word, w.length ≤ q.2.eval y.length ∧ next (pairB y w)) (fun y => y ∈ H) x

private def useful (H : Language Bool) (tail : List (Bool × Polynomial ℕ))
    (universal : Bool) (x w : Word) : Prop :=
  if universal then ¬ continueGame H tail (pairB x w) else continueGame H tail (pairB x w)

private theorem choose_move (he : P = NP) (H : Language Bool) (hH : H ∈ P)
    (tail : List (Bool × Polynomial ℕ)) (universal : Bool) (p : Polynomial ℕ) :
    ∃ choose : Word → Word,
      ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) choose ∧
      ∀ x : Word, (∃ w : Word, w.length ≤ p.eval x.length ∧ useful H tail universal x w) →
        (choose x).length ≤ p.eval x.length ∧ useful H tail universal x (choose x) ∧
        ∀ w : Word, w.length ≤ p.eval x.length → useful H tail universal x w →
          (choose x).length < w.length ∨ (choose x).length = w.length ∧
            (choose x = w ∨ List.Lex (fun a b => a = false ∧ b = true) (choose x) w) := by
  obtain ⟨L, hL, hspec⟩ := (FiniteQuantifiedWordCollapse.mp he) H hH tail
  have hgame (x : Word) : x ∈ L ↔ continueGame H tail x := hspec x
  let T : Language Bool := if universal then Lᶜ else L
  have hT : T ∈ P := by
    cases universal
    · exact hL
    · exact L008 L hL
  have hmem (x w : Word) : pairB x w ∈ T ↔ useful H tail universal x w := by
    cases universal
    · exact hgame _
    · exact not_congr (hgame _)
  let R : Set (Word × Word) := {q | pairB q.1 q.2 ∈ T}
  have hR : DecidableInPolyTime encodePair R := by
    obtain ⟨dec, hdec, htime⟩ := hT
    exact ⟨fun q => dec (pairB q.1 q.2), fun q => hdec _, cpt_comp cpt_pairB htime⟩
  obtain ⟨choose, htime, hs⟩ := (ShortestLexWitnessSearch.mp he) R p hR
  refine ⟨choose, htime, ?_⟩
  intro x hex
  obtain ⟨w, hw, ht⟩ := hex
  have h := hs x ⟨w, hw, (hmem x w).mpr ht⟩
  exact ⟨h.1, (hmem x (choose x)).mp h.2.1, fun v hv hV => h.2.2 v hv ((hmem x v).mpr hV)⟩

theorem PEqualNP.Outside.FiniteQuantifiedWordOptimalMove (he : P = NP)
    (H : Language Bool) (hH : H ∈ P) (tail : List (Bool × Polynomial ℕ))
    (universal : Bool) (p : Polynomial ℕ) :
    let after := fun x : List Bool =>
      tail.foldr (fun q next y =>
        let extend (w : List Bool) := List.replicate y.length true ++ false :: (y ++ w)
        if q.1 then ∀ w : List Bool, w.length ≤ q.2.eval y.length → next (extend w)
        else ∃ w : List Bool, w.length ≤ q.2.eval y.length ∧ next (extend w))
        (fun y => y ∈ H) x
    let useful := fun (x w : List Bool) =>
      let extended := List.replicate x.length true ++ false :: (x ++ w)
      if universal then ¬ after extended else after extended
    ∃ choose : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) choose ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ useful x w) →
        (choose x).length ≤ p.eval x.length ∧ useful x (choose x) ∧
        ∀ w : List Bool, w.length ≤ p.eval x.length → useful x w →
          (choose x).length < w.length ∨ (choose x).length = w.length ∧
            (choose x = w ∨ List.Lex (fun a b => a = false ∧ b = true) (choose x) w) :=
  choose_move he H hH tail universal p
