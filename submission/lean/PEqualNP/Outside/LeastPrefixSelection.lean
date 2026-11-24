import PEqualNP.Outside.PrefixSelector

namespace PEqualNP.Outside.LeastPrefixSelection

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.PrefixIteration (advance)
open PEqualNP.Outside.PrefixSelector (step step_cpt step_grows iterate_packed)

def LexLe (u v : Word) : Prop := u = v ∨ List.Lex (fun a b => a = false ∧ b = true) u v

private theorem nil_le (v : Word) : LexLe [] v := by
  cases v
  · exact Or.inl rfl
  · exact Or.inr List.Lex.nil

private theorem cons_le (b : Bool) {u v : Word} (h : LexLe u v) : LexLe (b :: u) (b :: v) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (List.Lex.cons h)

theorem remove_head (b : Bool) {u v : Word} (h : LexLe (b :: u) (b :: v)) :
    LexLe u v := by
  rcases h with he | hl
  · exact Or.inl (List.cons.inj he).2
  · cases hl with
    | rel hr => exact False.elim (Bool.noConfusion (hr.1.symm.trans hr.2))
    | cons ht => exact Or.inr ht

theorem pref_order (n m : ℕ) (u v : Word)
    (h : LexLe (List.replicate n true ++ false :: u) (List.replicate m true ++ false :: v)) :
    n < m ∨ n = m ∧ LexLe u v := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact Or.inr ⟨rfl, remove_head false h⟩
    | succ m => exact Or.inl (Nat.zero_lt_succ _)
  | succ n ih =>
    cases m with
    | zero =>
      change LexLe (true :: (List.replicate n true ++ false :: u)) (false :: v) at h
      rcases h with he | hl
      · simp at he
      · cases hl with
        | rel hr => exact False.elim (Bool.noConfusion hr.1)
    | succ m =>
      change LexLe (true :: (List.replicate n true ++ false :: u))
        (true :: (List.replicate m true ++ false :: v)) at h
      rcases ih m (remove_head true h) with hlt | ⟨he, hl⟩
      · exact Or.inl (Nat.succ_lt_succ hlt)
      · exact Or.inr ⟨congrArg Nat.succ he, hl⟩

theorem iterate_least (done canExtend : Word → Bool) (good : Word → Prop)
    (hd : ∀ pre, done pre = true ↔ good pre)
    (he : ∀ pre, canExtend pre = true ↔ ∃ s : Word, good (pre ++ s))
    (k : ℕ) (hlen : ∀ w, good w → w.length ≤ k)
    (n : ℕ) (pre : Word) (hbudget : k ≤ pre.length + n)
    (hex : ∃ s : Word, good (pre ++ s)) :
    ∃ s : Word, (advance done canExtend)^[n] pre = pre ++ s ∧
      good (pre ++ s) ∧ ∀ t : Word, good (pre ++ t) → LexLe s t := by
  induction n generalizing pre with
  | zero =>
    obtain ⟨s, hs⟩ := hex
    have h := hlen _ hs
    simp only [List.length_append, Nat.add_zero] at h hbudget
    have heq : s = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨[], by simp, heq ▸ hs, fun t _ => nil_le t⟩
  | succ n ih =>
    cases hdone : done pre
    · have hb (v : Bool) : k ≤ (pre ++ [v]).length + n := by
        simp only [List.length_append, List.length_singleton]
        omega
      cases hfalse : canExtend (pre ++ [false])
      · have next_suffix {t : Word} (ht : good (pre ++ t)) : ∃ r, t = true :: r := by
          cases t with
          | nil =>
            have hyes := (hd _).mpr (by simpa using ht)
            simp [hdone] at hyes
          | cons v r =>
            cases v
            · have hyes := (he (pre ++ [false])).mpr ⟨r, by simpa [List.append_assoc] using ht⟩
              simp [hfalse] at hyes
            · exact ⟨r, rfl⟩
        obtain ⟨t, ht⟩ := hex
        obtain ⟨r, rfl⟩ := next_suffix ht
        obtain ⟨s, hs, hgood, hbest⟩ :=
          ih (pre ++ [true]) (hb true) ⟨r, by simpa [List.append_assoc] using ht⟩
        refine ⟨true :: s, ?_, by simpa [List.append_assoc] using hgood, ?_⟩
        · rw [Function.iterate_succ_apply]
          have hstep : advance done canExtend pre = pre ++ [true] := by
            simp [advance, hdone, hfalse]
          rw [hstep, hs]
          simp [List.append_assoc]
        · intro t ht
          obtain ⟨r, rfl⟩ := next_suffix ht
          exact cons_le true (hbest r (by simpa [List.append_assoc] using ht))
      · obtain ⟨s, hs, hgood, hbest⟩ :=
          ih (pre ++ [false]) (hb false) ((he _).mp hfalse)
        refine ⟨false :: s, ?_, by simpa [List.append_assoc] using hgood, ?_⟩
        · rw [Function.iterate_succ_apply]
          have hstep : advance done canExtend pre = pre ++ [false] := by
            simp [advance, hdone, hfalse]
          rw [hstep, hs]
          simp [List.append_assoc]
        · intro t ht
          cases t with
          | nil =>
            have hyes := (hd _).mpr (by simpa using ht)
            simp [hdone] at hyes
          | cons b t =>
            cases b
            · exact cons_le false (hbest t (by simpa [List.append_assoc] using ht))
            · exact Or.inr (List.Lex.rel ⟨rfl, rfl⟩)
    · have hf : advance done canExtend pre = pre := by simp [advance, hdone]
      exact ⟨[], by simp [Function.iterate_fixed hf], by simpa using (hd _).mp hdone, fun t _ => nil_le t⟩

theorem selector_of_extensions (R : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (he : extensions R p ∈ P) :
    ∃ s : Word → Word,
      ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) s ∧
      ∀ x : Word, (∃ w : Word, good R p x w) → good R p x (s x) ∧
        ∀ w : Word, good R p x w → LexLe (s x) w := by
  obtain ⟨verify, hv, hc⟩ := hR
  obtain ⟨canExtend, he_spec, he_cpt⟩ := he
  let done : Word → Bool := fun z =>
    decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)
  let g := step done canExtend
  have hcpt := step_cpt (cpt_test verify p hc) he_cpt
  let s := fun x : Word => (unpairB (g^[p.eval x.length] (pairB x []))).2
  refine ⟨s, clocked_selector hcpt p (step_grows done canExtend), ?_⟩
  intro x hx
  have hd' : ∀ w : Word, done (pairB x w) = true ↔ good R p x w := by
    intro w
    simp only [done, unpairB_pairB, good, Bool.and_eq_true, decide_eq_true_eq, hv]
  have he' : ∀ w : Word, canExtend (pairB x w) = true ↔ ∃ t, good R p x (w ++ t) := by
    intro w
    rw [← he_spec]
    change (∃ t, good R p (unpairB (pairB x w)).1 ((unpairB (pairB x w)).2 ++ t)) ↔ _
    simp only [unpairB_pairB]
  obtain ⟨w, hw, hgood, hleast⟩ := iterate_least _ _ _ hd' he' (p.eval x.length)
    (fun _ h => h.1) (p.eval x.length) [] (by simp) (by simpa using hx)
  have hs : s x = w := by
    change (unpairB ((step done canExtend)^[p.eval x.length] (pairB x []))).2 = _
    rw [iterate_packed, unpairB_pairB, hw]
    rfl
  rw [hs]
  exact ⟨by simpa using hgood, by simpa using hleast⟩

end PEqualNP.Outside.LeastPrefixSelection
