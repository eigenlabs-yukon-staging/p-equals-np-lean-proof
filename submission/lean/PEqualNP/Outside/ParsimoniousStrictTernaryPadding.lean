import PEqualNP.Outside.UniqueTernaryPaddingDegree
import PEqualNP.Outside.ParsimoniousTableau

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.TernaryGadget (old extend extend_old)
open PEqualNP.Outside.OneHot (Models Mentioned eval_restrict)

def liftModel (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) (a : Models F) : Models (padFrom j F) :=
  ⟨fun i => extend (OneHot.extend F a.1) i.1,
    (eval_restrict ..).trans (pad_complete (OneHot.extend F a.1) F hF j a.2)⟩

def projectModel (F : CNF) (j : ℕ) (b : Models (padFrom j F)) : Models F :=
  ⟨fun i => OneHot.extend (padFrom j F) b.1 (old i.1),
    (eval_restrict ..).trans (pad_sound (OneHot.extend (padFrom j F) b.1) F j b.2)⟩

theorem project_lift (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) (a : Models F) :
    projectModel F j (liftModel F hF j a) = a := by
  apply Subtype.ext
  funext i
  have hM : Mentioned (padFrom j F) (old i.1) := (pad_vars F j i.1).mpr i.2
  change OneHot.extend (padFrom j F) (liftModel F hF j a).1 (old i.1) = a.1 i
  rw [show OneHot.extend (padFrom j F) (liftModel F hF j a).1 (old i.1) =
    (liftModel F hF j a).1 ⟨old i.1,hM⟩ from dite_eq_left hM]
  change extend (OneHot.extend F a.1) (old i.1) = a.1 i
  rw [extend_old]
  exact dite_eq_left i.2

theorem lift_project (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) (b : Models (padFrom j F)) :
    liftModel F hF j (projectModel F j b) = b := by
  apply Subtype.ext
  funext w
  let a := OneHot.extend (padFrom j F) b.1
  have hVal : a w.1 = b.1 w := dite_eq_left w.2
  change extend (OneHot.extend F (projectModel F j b).1) w.1 = b.1 w
  rw [← hVal]
  by_cases h : w.1%2 = 0
  · have e : old (w.1/2) = w.1 := by unfold old; omega
    have hM : Mentioned F (w.1/2) := (pad_vars F j _).mp (e.symm ▸ w.2)
    rw [← e,extend_old,
      show OneHot.extend F (projectModel F j b).1 (w.1/2) =
        (projectModel F j b).1 ⟨w.1/2,hM⟩ from dite_eq_left hM]
    rfl
  · have ho : w.1%2 = 1 := by omega
    simp only [extend,ite_eq_right h]
    exact (pad_fresh a F j w.1 ho w.2 b.2).symm

def modelEquiv (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) : Models F ≃ Models (padFrom j F) where
  toFun := liftModel F hF j
  invFun := projectModel F j
  left_inv := project_lift F hF j
  right_inv := lift_project F hF j

end PEqualNP.Outside.UniqueTernaryGadget

open PEqualNP.Search

theorem PEqualNP.Outside.ParsimoniousStrictTernaryPadding :
    ∀ F : CNF, IsKCNF 3 F →
      (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 5) →
      ∃ G : CNF,
        (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        (∀ v, (G.flatMap (List.map Prod.fst)).count v ≤ 5) ∧
        Nonempty (
          {a : {i : ℕ // i ∈ F.flatMap (List.map Prod.fst)} → Bool //
            CNF.eval (fun i => if h : i ∈ F.flatMap (List.map Prod.fst) then a ⟨i,h⟩ else false) F = true} ≃
          {a : {i : ℕ // i ∈ G.flatMap (List.map Prod.fst)} → Bool //
            CNF.eval (fun i => if h : i ∈ G.flatMap (List.map Prod.fst) then a ⟨i,h⟩ else false) G = true}) := by
  intro F hW hD
  open PEqualNP.Outside.UniqueTernaryGadget in
  exact ⟨padFrom 0 F,pad_shape F hW 0,pad_degree F 0 hD,⟨modelEquiv F hW 0⟩⟩
