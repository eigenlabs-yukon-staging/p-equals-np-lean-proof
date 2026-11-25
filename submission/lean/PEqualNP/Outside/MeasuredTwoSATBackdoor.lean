import PEqualNP.Outside.TwoSATDeletionBackdoor
import PEqualNP.Outside.CNFWideClausePacking
import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

private abbrev Raw := List Bool
private abbrev Change := Raw × Raw → Raw

private def widePart (pack : Raw → Raw) (s : Raw) : Raw := (unpairB (pack (unpairB s).1)).2
private def key (u : Raw) : Raw := (headI u).tail.tail
private def child (erase rest : Change) (suffix s : Raw) : Raw :=
  pairB (erase (key suffix,(unpairB s).1)) (rest (key suffix,(unpairB s).2))

private theorem child_cpt {erase rest : Change}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hr : ComputableInPolyTime encodePair (fun x : Raw => x) rest)
    {suffix : Raw → Raw} (hs : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) suffix) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => child erase rest (suffix s) s) := by
  have hk := cpt_tail1 (cpt_tail1 (cpt_comp hs cpt_headI))
  exact cpt_pairB2 (cpt_comp (cpt_pair hk cpt_unpairB1) he) (cpt_comp (cpt_pair hk cpt_unpairB2) hr)

private def both (f : Raw → Raw) (erase pos neg : Change) (suffix s : Raw) : Raw :=
  f (child erase pos suffix s) ++ f (child erase neg suffix s)

private theorem both_cpt {f : Raw → Raw} {erase pos neg : Change} {suffix : Raw → Raw}
    (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg)
    (hs : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) suffix) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x)
      (fun s => both f erase pos neg (suffix s) s) :=
  cpt_app2 (cpt_comp (child_cpt he hp hs) hf) (cpt_comp (child_cpt he hn hs) hf)

private def search (pack : Raw → Raw) (erase pos neg : Change) (base : Raw → Raw) : ℕ → Raw → Raw
  | 0, s => sel (widePart pack s) (base (unpairB s).2) []
  | k+1, s =>
      let u := widePart pack s
      let f := search pack erase pos neg base k
      sel u (base (unpairB s).2)
        (both f erase pos neg u s ++ both f erase pos neg (dropI u) s ++
          both f erase pos neg (dropI (dropI u)) s)

private theorem search_cpt {pack : Raw → Raw} {erase pos neg : Change} {base : Raw → Raw}
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) pack)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg)
    (hb : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) base) (k : ℕ) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (search pack erase pos neg base k) := by
  have hu : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (widePart pack) :=
    cpt_unpairB2_1 (cpt_comp cpt_unpairB1 hw)
  have ht := cpt_comp cpt_unpairB2 hb
  induction k with
  | zero => exact cpt_sel hu ht (cpt_const [])
  | succ k hf =>
      have hu₁ := cpt_comp hu cpt_dropI
      have hu₂ := cpt_comp hu₁ cpt_dropI
      exact cpt_sel hu ht (cpt_app2 (cpt_app2 (both_cpt hf he hp hn hu)
        (both_cpt hf he hp hn hu₁)) (both_cpt hf he hp hn hu₂))

private theorem encode_cons (l : Literal) (c : Clause) (φ : CNF) :
    encodeCNF ((l :: c) :: φ) = encodeLiteral l ++ (encodeClause c ++ encodeCNF φ) := by
  simp [encodeCNF,encodeClause,List.append_assoc]

private theorem key_head (l : Literal) (c : Clause) (φ : CNF) :
    key (encodeCNF ((l :: c) :: φ)) = vcode l.1 := by
  unfold key
  rw [encode_cons,headI_lit,encodeLiteral_eq]
  rfl

private theorem drop_head (l : Literal) (c : Clause) (φ : CNF) :
    dropI (encodeCNF ((l :: c) :: φ)) = encodeCNF (c :: φ) := by
  rw [encode_cons,dropI_lit]
  simp [encodeCNF]

private theorem encoding_ne_nil {φ : CNF} (h : φ ≠ []) : encodeCNF φ ≠ [] := by
  intro he
  exact h (encodeCNF_injective (he.trans (show [] = encodeCNF [] by rfl)))

private theorem short_iff_empty (φ : CNF) :
    ((φ.filter (fun c => 2 < c.length)).reverse) = [] ↔ IsKCNF 2 φ := by
  rw [List.reverse_eq_nil_iff,List.filter_eq_nil_iff]
  simp [IsKCNF,decide_eq_true_eq]

private theorem exists_branch (f : Raw → Raw) (erase pos neg : Change) (φ ψ : CNF)
    (hp : ∀ x φ, pos (vcode x,encodeCNF φ) = encodeCNF (restrict x true φ))
    (hn : ∀ x φ, neg (vcode x,encodeCNF φ) = encodeCNF (restrict x false φ))
    (he : ∀ x φ, erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ))
    (l : Literal) (c : Clause) (φ' : CNF) :
    both f erase pos neg (encodeCNF ((l :: c) :: φ')) (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔
    ∃ b : Bool, f (pairB (encodeCNF (eraseVariable l.1 φ)) (encodeCNF (restrict l.1 b ψ))) ≠ [] := by
  simp only [both,child,key_head,unpairB_pairB,he,hp,hn,ne_eq,List.append_eq_nil_iff,not_and_or]
  constructor
  · rintro (h | h)
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  · rintro ⟨b,h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h

private theorem search_correct (pack : Raw → Raw) (erase pos neg : Change) (base : Raw → Raw)
    (hw : ∀ φ, widePart pack (pairB (encodeCNF φ) []) =
      encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse))
    (he : ∀ x φ, erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ))
    (hp : ∀ x φ, pos (vcode x,encodeCNF φ) = encodeCNF (restrict x true φ))
    (hn : ∀ x φ, neg (vcode x,encodeCNF φ) = encodeCNF (restrict x false φ))
    (hb : ∀ φ, IsKCNF 2 φ → (base (encodeCNF φ) ≠ [] ↔ Satisfiable φ))
    (k : ℕ) (φ ψ : CNF) (hsub : ψ.Sublist φ) :
    search pack erase pos neg base k (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔
      widthTwoBackdoor k φ ∧ Satisfiable ψ := by
  have hwide (φ ψ : CNF) : widePart pack (pairB (encodeCNF φ) (encodeCNF ψ)) =
      encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) := by
    have h := hw φ
    simpa only [widePart,unpairB_pairB] using h
  induction k generalizing φ ψ with
  | zero =>
      by_cases h : IsKCNF 2 φ
      · have hn' := (short_iff_empty φ).mpr h
        simp only [search,hwide,hn',show encodeCNF [] = [] by rfl,sel,ite_true,unpairB_pairB,
          hb ψ (width_sublist hsub h), backdoor_zero, h, true_and]
      · have hn' := encoding_ne_nil (fun hh => h ((short_iff_empty φ).mp hh))
        simp [search,hwide,sel,hn',backdoor_zero,h]
  | succ k ih =>
      let u := (φ.filter (fun c => 2 < c.length)).reverse
      cases hu : u with
      | nil =>
          have h := (short_iff_empty φ).mp hu
          have hpart := hwide φ ψ
          change _ = encodeCNF u at hpart
          rw [hu] at hpart
          simp only [search,hpart,show encodeCNF [] = [] by rfl,sel,ite_true,unpairB_pairB,
            hb ψ (width_sublist hsub h),backdoor_done (k+1) h,true_and]
      | cons d ds =>
          have hmem : d ∈ u := hu.symm ▸ List.mem_cons_self
          have hraw := List.mem_filter.mp (List.mem_reverse.mp hmem)
          have hlen : 2 < d.length := of_decide_eq_true hraw.2
          cases d with
          | nil => simp at hlen
          | cons l₁ d =>
              cases d with
              | nil => simp at hlen
              | cons l₂ d =>
                  cases d with
                  | nil => simp at hlen
                  | cons l₃ r =>
                      have hhit := backdoor_triple k l₁ l₂ l₃ r φ hraw.1
                      have hpart := hwide φ ψ
                      change _ = encodeCNF u at hpart
                      rw [hu] at hpart
                      have hn' := encoding_ne_nil (List.cons_ne_nil (l₁ :: l₂ :: l₃ :: r) ds)
                      simp only [search,hpart,sel,ite_eq_right hn',drop_head,ne_eq,List.append_eq_nil_iff,
                        not_and_or,exists_branch _ _ _ _ _ _ hp hn he,hhit]
                      have recurse (x : ℕ) :
                          (∃ b : Bool, search pack erase pos neg base k
                            (pairB (encodeCNF (eraseVariable x φ)) (encodeCNF (restrict x b ψ))) ≠ []) ↔
                          (widthTwoBackdoor k (eraseVariable x φ) ∧ Satisfiable ψ) := by
                        constructor
                        · rintro ⟨b,h⟩
                          obtain ⟨hd,hs⟩ := (ih _ _ (restrict_sublist_erase x b hsub)).mp h
                          exact ⟨hd,(satisfiable_split ψ x).mpr ⟨b,hs⟩⟩
                        · rintro ⟨hd,hs⟩
                          obtain ⟨b,hs'⟩ := (satisfiable_split ψ x).mp hs
                          exact ⟨b,(ih _ _ (restrict_sublist_erase x b hsub)).mpr ⟨hd,hs'⟩⟩
                      simp only [recurse,List.mem_cons,List.not_mem_nil,or_false]
                      constructor
                      · rintro ((⟨h,hs⟩ | ⟨h,hs⟩) | ⟨h,hs⟩)
                        · exact ⟨⟨_,Or.inl rfl,h⟩,hs⟩
                        · exact ⟨⟨_,Or.inr (Or.inl rfl),h⟩,hs⟩
                        · exact ⟨⟨_,Or.inr (Or.inr rfl),h⟩,hs⟩
                      · rintro ⟨⟨x,hx,h⟩,hs⟩
                        rcases hx with he | he | he
                        · subst x; exact Or.inl (Or.inl ⟨h,hs⟩)
                        · subst x; exact Or.inl (Or.inr ⟨h,hs⟩)
                        · subst x; exact Or.inr ⟨h,hs⟩

/-- Fixed-size 2-CNF deletion backdoors can be recognized and used for SAT
in the same measured raw machine. The residual CNF can be a sublist. -/
theorem MeasuredTwoSATBackdoor (k : ℕ) :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ ψ : CNF), ψ.Sublist φ → (test (encodeCNF φ,encodeCNF ψ) = true ↔
        (∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2
          (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧ Satisfiable ψ) := by
  obtain ⟨pack,hpack,hs⟩ := CNFWideClausePacking
  obtain ⟨erase,he,hes⟩ := MeasuredVariableRestriction none
  obtain ⟨pos,hp,hps⟩ := MeasuredVariableRestriction (some true)
  obtain ⟨neg,hn,hns⟩ := MeasuredVariableRestriction (some false)
  obtain ⟨det,hdet,hc⟩ := L030
  let raw := search pack erase pos neg (fun x => if det x then [true] else []) k
  let test := fun p : List Bool × List Bool => !(raw (pairB p.1 p.2)).isEmpty
  have ht : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (g := fun w : List Bool => !w.isEmpty)
      (cpt_comp (g := raw) cpt_pairB (search_cpt hpack he hp hn (cpt_bitFlag hc) k)) bf_cpt_neL
  refine ⟨test,ht,fun φ ψ hsub => ?_⟩
  change (!(raw (pairB (encodeCNF φ) (encodeCNF ψ))).isEmpty) = true ↔ _
  simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff]
  have hparts (φ : CNF) : widePart pack (pairB (encodeCNF φ) []) =
      encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) := by
    unfold widePart
    rw [unpairB_pairB,hs]
    change (unpairB (pairB _ _)).2 = _
    simp only [unpairB_pairB]
  have her (x : ℕ) (φ : CNF) : erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ) := by
    simpa [eraseVariable,vcode] using hes x φ
  have hbase (φ : CNF) (hφ : IsKCNF 2 φ) :
      (if det (encodeCNF φ) then [true] else []) ≠ [] ↔ Satisfiable φ := by
    have hab : (if det (encodeCNF φ) then [true] else []) ≠ [] ↔ det (encodeCNF φ) = true := by
      cases det (encodeCNF φ) <;> decide
    rw [hab,← hdet]
    constructor
    · rintro ⟨ψ,_,he,hs⟩
      exact encodeCNF_injective he ▸ hs
    · intro h
      exact ⟨φ,hφ,rfl,h⟩
  exact search_correct pack erase pos neg _ hparts her hps hns hbase k φ ψ hsub

end PEqualNP.Outside
