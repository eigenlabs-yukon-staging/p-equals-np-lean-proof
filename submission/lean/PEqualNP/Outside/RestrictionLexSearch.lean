import PEqualNP.Outside.RestrictionSearchSemantics

namespace PEqualNP.Outside.RestrictionLexSearch

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.FirstWideCollector (Word pack)
open PEqualNP.Outside.TwoSatGreedyCore (step finish trueNames)
open PEqualNP.Outside.RestrictionSearchSemantics
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)
open PEqualNP.Outside.HornRenameMachine (flips)

abbrev Item := Option Literal

def itemCode : Item → Word
  | none => [false, false]
  | some l => encodeLiteral l

def items (φ : CNF) : List Item := φ.flatMap (fun c => c.map some ++ [none])

def bits (σ : Assignment) (ts : List Item) : Word := ts.filterMap (fun t => t.map (fun l => σ l.1))

def LexLe (xs ys : Word) : Prop :=
  xs = ys ∨ List.Lex (fun x y => x = false ∧ y = true) xs ys

theorem lex_cons (b : Bool) (x y : Word) (h : LexLe x y) : LexLe (b :: x) (b :: y) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (List.Lex.cons h)

theorem items_enc (φ : CNF) : (items φ).flatMap itemCode = encodeCNF φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have h (c : Clause) : (c.map some).flatMap itemCode = c.flatMap encodeLiteral := by
      induction c with
      | nil => rfl
      | cons l c ih => simp [itemCode, ih]
    simp [items, List.flatMap_append, h, itemCode, encodeCNF, encodeClause, List.append_assoc] at ih ⊢
    exact ih

theorem items_count (φ : CNF) : (items φ).length = nIt φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp [items, nIt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at ih ⊢
    omega

theorem bits_enc (σ : Assignment) (φ : CNF) :
    bits σ (items φ) = (φ.flatMap id).map (fun l => σ l.1) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have h (c : Clause) : bits σ (c.map some) = c.map (fun l => σ l.1) := by
      induction c with
      | nil => rfl
      | cons l c ih => simp [bits, ih]
    change bits σ ((c.map some ++ [none]) ++ items cs) = _
    simp only [bits, List.filterMap_append, List.filterMap_cons, Option.map_none, List.filterMap_nil,
      List.append_nil, List.flatMap_cons, List.map_append, id_eq] at *
    exact congrArg₂ List.append (h c) ih

theorem agrees_valueOf (s v : List ℕ) (σ : Assignment)
    (h : ∀ i ∈ s, σ i = flips v i) :
    ∀ i b, valueOf s v i = some b → σ i = b := by
  intro i b hi
  by_cases hm : i ∈ s
  · have hs := h i hm
    rw [hs]
    simpa [valueOf, flips, hm] using hi
  · simp [valueOf, hm] at hi

theorem extends_false_if (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec) (φ : CNF) (hF : φ ∈ F) (s v : List ℕ) (i : ℕ)
    (hi : i ∉ s) (hsubset : ∀ i ∈ v, i ∈ s)
    (σ : Assignment) (hσ : CNF.eval σ φ = true) (hag : ∀ j ∈ s, σ j = flips v j)
    (hb : σ i = false) :
    dec (encodeCNF (restrict (valueOf (s ++ [i]) v) φ)) = true := by
  have he : ∀ j ∈ s ++ [i], σ j = flips v j := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hag j hj
    · obtain rfl := List.mem_singleton.mp hj
      have hno : j ∉ v := fun hv => hi (hsubset j hv)
      simp [flips, hno, hb]
  exact (hd _ (hclosed _ _ hF)).mp ((sat_restrict_iff _ _).mpr
    ⟨σ, hσ, agrees_valueOf _ _ _ he⟩)

def invariant (φ : CNF) (ts : List Item) (s v s' v' : List ℕ) : Prop :=
  permitted φ s' v' ∧ (∀ i ∈ s, i ∈ s' ∧ flips v' i = flips v i) ∧
    (∀ l : Literal, some l ∈ ts → l.1 ∈ s') ∧
    ∀ σ : Assignment, CNF.eval σ φ = true → (∀ i ∈ s, σ i = flips v i) →
      LexLe (bits (flips v') ts) (bits σ ts)

theorem scan (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec) (φ : CNF) (hF : φ ∈ F)
    (ts : List Item) (s v : List ℕ) (hp : permitted φ s v) :
    ∃ s' v' : List ℕ,
      (step dec)^[ts.length] (state φ (ts.flatMap itemCode) s v) = state φ [] s' v' ∧
      invariant φ ts s v s' v' := by
  induction ts generalizing s v with
  | nil =>
    refine ⟨s, v, rfl, hp, fun i hi => ⟨hi, rfl⟩, by simp, ?_⟩
    exact fun _ _ _ => Or.inl rfl
  | cons t ts ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons]
    cases t with
    | none =>
      change ∃ s' v', (step dec)^[ts.length]
        (step dec (state φ ([false, false] ++ ts.flatMap itemCode) s v)) = _ ∧ _
      rw [step_close]
      obtain ⟨s', v', he, hq⟩ := ih s v hp
      exact ⟨s', v', he, by simpa [invariant, bits] using hq⟩
    | some l =>
      change ∃ s' v', (step dec)^[ts.length]
        (step dec (state φ (encodeLiteral l ++ ts.flatMap itemCode) s v)) = _ ∧ _
      by_cases hk : l.1 ∈ s
      · rw [step_lit_known dec φ l _ s v hk]
        obtain ⟨s', v', he, hpermit, hkeep, hmem, hlex⟩ := ih s v hp
        refine ⟨s', v', he, hpermit, hkeep, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with heq | hm
          · cases heq
            exact (hkeep _ hk).1
          · exact hmem _ hm
        · intro σ hσ hσ0
          have heq := (hkeep _ hk).2.trans (hσ0 _ hk).symm
          simp only [bits, List.filterMap_cons, Option.map_some]
          rw [heq]
          exact lex_cons _ _ _ (hlex σ hσ hσ0)
      · rw [step_lit_new dec φ l _ s v hk]
        let i := l.1
        let f := dec (encodeCNF (restrict (valueOf (s ++ [i]) v) φ))
        let w := v ++ if f then [] else [i]
        have hi : i ∉ v := fun hv => hk (hp.1 i hv)
        have hkeep (j : ℕ) (hj : j ∈ s) : flips w j = flips v j := by
          have hn : j ≠ i := fun h => hk (by simpa [i, h] using hj)
          cases hf : f <;> simp [flips, w, hf, hn]
        have hbit : flips w i = !f := by
          cases hf : f <;> simp [flips, w, hf, hi]
        have hnew := extension F hclosed dec hd φ hF s v i hk hp
        obtain ⟨s', v', he, hpermit, hout, hmem, hlex⟩ := ih (s ++ [i]) w hnew
        have hiNew : i ∈ s ++ [i] := by simp
        have hval : flips v' i = !f := (hout i hiNew).2.trans hbit
        refine ⟨s', v', he, hpermit, ?_, ?_, ?_⟩
        · intro j hj
          have he := hout j (List.mem_append_left _ hj)
          exact ⟨he.1, he.2.trans (hkeep j hj)⟩
        · intro a ha
          rcases List.mem_cons.mp ha with heq | hm
          · cases heq
            exact (hout i hiNew).1
          · exact hmem _ hm
        · intro σ hσ hσ0
          have try_false : σ i = false → f = true :=
            extends_false_if F hclosed dec hd φ hF s v i hk hp.1 σ hσ hσ0
          simp only [bits, List.filterMap_cons, Option.map_some]
          change LexLe (flips v' i :: bits (flips v') ts) (σ i :: bits σ ts)
          by_cases heq : σ i = flips w i
          · have he' (j : ℕ) (hj : j ∈ s ++ [i]) : σ j = flips w j := by
              rcases List.mem_append.mp hj with hj | hj
              · exact (hσ0 j hj).trans (hkeep j hj).symm
              · obtain rfl := List.mem_singleton.mp hj
                exact heq
            rw [(hout i hiNew).2, ← heq]
            exact lex_cons _ _ _ (hlex σ hσ he')
          · cases hσi : σ i
            · have hf := try_false hσi
              have hv : flips w i = false := by simp [hbit, hf]
              exact False.elim (heq (hσi.trans hv.symm))
            · have hv : flips w i = false := by
                cases h' : flips w i
                · rfl
                · exact False.elim (heq (hσi.trans h'.symm))
              rw [(hout i hiNew).2, hv]
              exact Or.inr (List.Lex.rel ⟨rfl, rfl⟩)

theorem solve (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec) (φ : CNF) (hF : φ ∈ F) (hsat : Satisfiable φ) :
    ∃ v : List ℕ, finish dec (encodeCNF φ, encodeCNF φ) = names v ∧
      CNF.eval (flips v) φ = true ∧
      ∀ σ : Assignment, CNF.eval σ φ = true →
        LexLe ((φ.flatMap id).map (fun l => flips v l.1)) ((φ.flatMap id).map (fun l => σ l.1)) := by
  have hp : permitted φ [] [] := by
    refine ⟨by simp, ?_⟩
    obtain ⟨σ, hσ⟩ := hsat
    exact (sat_restrict_iff _ _).mpr ⟨σ, hσ, by simp [valueOf]⟩
  obtain ⟨s, v, he, hpermit, _, hcover, hlex⟩ := scan F hclosed dec hd φ hF (items φ) [] [] hp
  rw [items_enc, items_count] at he
  refine ⟨v, ?_, ?_, ?_⟩
  · have hn := nIt_le φ
    change trueNames ((step dec)^[(encodeCNF φ).length] (state φ (encodeCNF φ) [] [])) = _
    rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he,
      Function.iterate_fixed (step_end dec φ s v)]
    simp [trueNames, state, pack, unpairB_pairB]
  · obtain ⟨σ, hσ, hag⟩ := (sat_restrict_iff _ _).mp hpermit.2
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨l, hl, ht⟩ := List.any_eq_true.mp (List.all_eq_true.mp hσ c hc)
    have hmem : some l ∈ items φ :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)⟩
    have hv : σ l.1 = flips v l.1 := by
      apply hag l.1
      simp [valueOf, flips, hcover l hmem]
    exact List.any_eq_true.mpr ⟨l, hl, by simpa [Literal.eval, hv] using ht⟩
  · intro σ hσ
    simpa only [bits_enc] using hlex σ hσ (by simp)

end PEqualNP.Outside.RestrictionLexSearch
