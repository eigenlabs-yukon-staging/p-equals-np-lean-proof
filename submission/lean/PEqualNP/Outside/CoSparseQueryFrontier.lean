import PEqualNP.Outside.FrontierExpansionMachine
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def memberTest (seen query : Word) : Bool :=
  imageLookup (fun p => p.2) (pairB [] (pairB query seen))

private theorem memberTest_spec (xs : List Word) (x : Word) :
    memberTest (encodeFrontier xs) x = true ↔ x ∈ xs := by
  change imageLookup (fun p => p.2) (pairB [] (pairB x (xs.foldr pairB []))) = true ↔ _
  rw [imageLookup_spec]
  dsimp only
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private def memberFlag (p : Word × Word) : Word := bflag (memberTest p.1 p.2)

private theorem memberFlag_cpt : ComputableInPolyTime encodePair (fun x => x) memberFlag := by
  have h := cpt_comp cpt_pairB
    (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB2 cpt_unpairB1))
  have hc := cpt_bitFlag (cpt_comp h (imageLookup_polyTime cpt_snd))
  apply bf_cptl hc
  rintro ⟨seen, q⟩
  by_cases he : imageLookup (fun p => p.2) (pairB [] (pairB q seen)) = true <;>
    simp [memberFlag, memberTest, unpairB_pairB, bflag, he]

def freshQuery (seen rawQueries : Word) : Bool :=
  imageLookup memberFlag (pairB seen (pairB [] rawQueries))

theorem freshQuery_cpt {seen queries : Word → Word} (hs : CPT seen) (hq : CPT queries) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool (fun x => freshQuery (seen x) (queries x)) :=
  bf_cptl (cpt_comp (cpt_pairB2 hs (cpt_pairB2 (cpt_const []) hq))
    (imageLookup_polyTime memberFlag_cpt)) (fun _ => rfl)

theorem freshQuery_spec (seen qs : List Word) :
    freshQuery (encodeFrontier seen) (encodeFrontier qs) = true ↔ ∃ x ∈ qs, x ∉ seen := by
  change imageLookup memberFlag (pairB (encodeFrontier seen) (pairB [] (qs.foldr pairB []))) = true ↔ _
  rw [imageLookup_spec]
  simp only [memberFlag, bflag_eq_nil]
  have hb (x : Word) : memberTest (encodeFrontier seen) x = false ↔ x ∉ seen := by
    rw [← memberTest_spec seen x]
    cases memberTest (encodeFrontier seen) x <;> simp
  simp only [hb]

private def retainNew (queries : Word → List Word) (seen : List Word) :
    List Word → List Word × List Word
  | [] => (seen, [])
  | x :: xs =>
    if ∃ w ∈ queries x, w ∉ seen then
      let (seen', keep) := retainNew queries (seen ++ queries x) xs
      (seen', x :: keep)
    else retainNew queries seen xs

private theorem retainNew_spec (queries : Word → List Word) (seen xs : List Word) :
    let (seen', keep) := retainNew queries seen xs
    keep.Sublist xs ∧
    seen.toFinset.card + keep.length ≤ seen'.toFinset.card ∧
    (∀ z, z ∈ seen' ↔ z ∈ seen ∨ ∃ x ∈ xs, z ∈ queries x) ∧
    (∀ z, z ∈ seen' ↔ z ∈ seen ∨ ∃ x ∈ keep, z ∈ queries x) := by
  classical
  induction xs generalizing seen with
  | nil => simp [retainNew]
  | cons x xs ih =>
    by_cases hf : ∃ w ∈ queries x, w ∉ seen
    · obtain ⟨w, hw, hn⟩ := hf
      rcases e : retainNew queries (seen ++ queries x) xs with ⟨next, keep⟩
      have h := ih (seen ++ queries x)
      rw [e] at h
      obtain ⟨hsub, hcount, heq, heqKeep⟩ := h
      have hlt : seen.toFinset.card < (seen ++ queries x).toFinset.card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro z hz
          exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hz))
        · intro hsame
          apply hn
          apply List.mem_toFinset.mp
          rw [hsame]
          exact List.mem_toFinset.mpr (List.mem_append_right _ hw)
      have hf : ∃ z ∈ queries x, z ∉ seen := ⟨w, hw, hn⟩
      simp only [retainNew, hf, ite_true, e]
      refine ⟨hsub.cons_cons x, by simp; omega, ?_, ?_⟩
      · intro z
        rw [heq]
        simp [List.mem_append, or_assoc]
      · intro z
        rw [heqKeep]
        simp [List.mem_append, or_assoc]
    · rcases e : retainNew queries seen xs with ⟨next, keep⟩
      have h := ih seen
      rw [e] at h
      obtain ⟨hsub, hc, heq, heqKeep⟩ := h
      simp only [retainNew, hf, ite_false, e]
      refine ⟨hsub.cons x, hc, ?_, heqKeep⟩
      intro z
      rw [heq]
      constructor
      · intro hz
        rcases hz with hm | ⟨y, hy, hz⟩
        · exact Or.inl hm
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hz⟩
      · rintro (hm | ⟨y, hy, hz⟩)
        · exact Or.inl hm
        · rcases List.mem_cons.mp hy with rfl | hh
          · exact Or.inl (by by_contra h; exact hf ⟨z, hz, h⟩)
          · exact Or.inr ⟨y, hh, hz⟩

private def coverStep (g : Word → Word) (s : Word) : Word :=
  let cap := (unpairB s).1
  let tail := (unpairB s).2
  let todo := (unpairB tail).1
  let data₀ := (unpairB tail).2
  let seen := (unpairB data₀).1
  let data₁ := (unpairB data₀).2
  let count := (unpairB data₁).1
  let kept := (unpairB data₁).2
  let x := (unpairB todo).1
  let xs := (unpairB todo).2
  let q := g x
  let small := bflag (decide (q.length ≤ cap.length))
  let fresh := bflag (freshQuery seen q)
  let kept' := pairB (seen ++ q) (pairB (true :: count) (kept ++ pairB x []))
  let next := pairB cap (pairB xs (sel small data₀ (sel fresh data₀ kept')))
  sel todo s next

private def coverMeasure (s : Word) : Nat := 2 * (unpairB s).1.length + 7

private theorem coverMeasure_step (g : Word → Word) (s : Word) :
    coverMeasure (coverStep g s) ≤ coverMeasure s := by
  unfold coverStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [coverMeasure, unpairB_pairB]

private theorem coverStep_size (g : Word → Word) (s : Word) :
    (coverStep g s).length ≤ s.length + coverMeasure s := by
  have hs := unpairB_length s
  have h₀ := unpairB_length (unpairB s).2
  have h₁ := unpairB_length (unpairB (unpairB s).2).2
  have h₂ := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  have ht := unpairB_length (unpairB (unpairB s).2).1
  unfold coverStep coverMeasure
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length]
    split
    · omega
    · rename_i hne
      have hsmall := (not_congr (bflag_eq_nil _)).mp hne
      simp only [Bool.not_eq_false, decide_eq_true_eq] at hsmall
      split
      · omega
      · simp only [pairB_length, List.length_append, List.length_cons, List.length_nil]
        omega

private theorem coverStep_cpt {g : Word → Word} (hg : CPT g) : CPT (coverStep g) := by
  have hcap := cpt_unpairB1
  have ht := cpt_unpairB1_1 cpt_unpairB2
  have hData := cpt_unpairB2_1 cpt_unpairB2
  have hs := cpt_unpairB1_1 hData
  have hc := cpt_unpairB1_1 (cpt_unpairB2_1 hData)
  have hk := cpt_unpairB2_1 (cpt_unpairB2_1 hData)
  have hx := cpt_unpairB1_1 ht
  have hq := cpt_comp hx hg
  have hsmall := cpt_bitFlag (cpt_comp (cpt_pair hcap hq) LenCmp.lenLE_polyTime)
  have hfresh := cpt_bitFlag (freshQuery_cpt hs hq)
  have hkeep := cpt_pairB2 (cpt_app2 hs hq)
    (cpt_pairB2 (cpt_cons1 true hc) (cpt_app2 hk (cpt_pairB2 hx (cpt_const []))))
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hcap (cpt_pairB2 (cpt_unpairB2_1 ht)
    (cpt_sel hsmall hData (cpt_sel hfresh hData hkeep))))) (fun _ => rfl)

private def coverState (cap : Word) (xs seen kept : List Word) (count : Word) : Word :=
  pairB cap (pairB (encodeFrontier xs) (pairB (encodeFrontier seen) (pairB count (encodeFrontier kept))))

private theorem coverStep_cons (g : Word → Word) (qs : Word → List Word)
    (gs : ∀ x, g x = encodeFrontier (qs x)) (cap : Word) (x : Word)
    (xs seen kept : List Word) (cnt : Word) (hc : (g x).length ≤ cap.length) :
    coverStep g (coverState cap (x :: xs) seen kept cnt) =
      if ∃ w ∈ qs x, w ∉ seen then coverState cap xs (seen ++ qs x) (kept ++ [x]) (true :: cnt)
      else coverState cap xs seen kept cnt := by
  have es : encodeFrontier (x :: xs) = pairB x (encodeFrontier xs) := rfl
  have en : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
  have hf := freshQuery_spec seen (qs x)
  have hsize : (encodeFrontier (qs x)).length ≤ cap.length := by simpa [gs] using hc
  have hsingle : encodeFrontier [x] = pairB x [] := rfl
  by_cases h : ∃ w ∈ qs x, w ∉ seen
  · simp [coverStep, coverState, es, en, unpairB_pairB, sel, bflag, h, hf.mpr h, hsize,
      gs, encodeFrontier_append_words, hsingle]
  · have hn : freshQuery (encodeFrontier seen) (encodeFrontier (qs x)) = false := by
      cases he : freshQuery (encodeFrontier seen) (encodeFrontier (qs x))
      · rfl
      · exact False.elim (h (hf.mp he))
    simp [coverStep, coverState, es, en, unpairB_pairB, sel, bflag, h, hn, hsize, gs]

private theorem coverIter_spec (qs : Word → List Word) (g : Word → Word)
    (gs : ∀ x, g x = encodeFrontier (qs x)) (cap : Word) (xs : List Word) :
    ∀ n : Nat, xs.length ≤ n → ∀ (seen kept : List Word) (cnt : Word),
      (∀ x ∈ xs, (g x).length ≤ cap.length) →
      let (seen', keep') := retainNew qs seen xs
      (coverStep g)^[n] (coverState cap xs seen kept cnt) =
        coverState cap [] seen' (kept ++ keep') (List.replicate keep'.length true ++ cnt) := by
  induction xs with
  | nil =>
    intro n _ seen kept cnt _
    have hf : coverStep g (coverState cap [] seen kept cnt) = coverState cap [] seen kept cnt := by
      simp [coverStep, coverState, encodeFrontier, unpairB_pairB]
    simpa [retainNew] using Function.iterate_fixed hf n
  | cons x xs ih =>
    intro n hn seen kept cnt hb
    cases n with
    | zero => simp at hn
    | succ n =>
      dsimp only
      rw [Function.iterate_succ_apply, coverStep_cons g qs gs cap x xs seen kept cnt (hb x List.mem_cons_self)]
      have hs : ∀ y ∈ xs, (g y).length ≤ cap.length :=
        fun y hy => hb y (List.mem_cons_of_mem _ hy)
      have hle : xs.length ≤ n := by simpa using hn
      by_cases h : ∃ w ∈ qs x, w ∉ seen
      · rw [if_pos h]
        rcases e : retainNew qs (seen ++ qs x) xs with ⟨new, retained⟩
        have h' := ih n hle (seen ++ qs x) (kept ++ [x]) (true :: cnt) hs
        rw [e] at h'
        simpa [retainNew, h, e, List.replicate_succ', List.append_assoc] using h'
      · rw [if_neg h]
        simpa [retainNew, h] using ih n hle seen kept cnt hs

private def coverScan (g : Word → Word) (r : Polynomial Nat) (s : Word) : Word :=
  let cap := un (r.eval s.length)
  let out := (coverStep g)^[s.length] (pairB cap (pairB s (pairB [] (pairB [] []))))
  (unpairB (unpairB (unpairB out).2).2).2

private theorem coverScan_cpt {g : Word → Word} (hg : CPT g) (r : Polynomial Nat) :
    CPT (coverScan g r) := by
  obtain ⟨c⟩ := coverStep_cpt hg
  have h := Iter.iter_polyTime_measure (coverStep g) c coverMeasure 7
    (coverMeasure_step g) (coverStep_size g) (fun s => by
      have he := unpairB_length s
      unfold coverMeasure
      omega)
  have hinit := cpt_pairB2 (L055 r) (cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] []))))
  have hs := cpt_comp (cpt_pair hinit cpt_id) h
  exact bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hs))) (fun _ => rfl)

private theorem coverScan_spec (qs : Word → List Word) (g : Word → Word) (r : Polynomial Nat)
    (gs : ∀ x, g x = encodeFrontier (qs x)) (hr : ∀ x, (g x).length ≤ r.eval (List.length x))
    (xs : List Word) :
    let keep := (retainNew qs [] xs).2
    coverScan g r (encodeFrontier xs) = pairB (un keep.length) (encodeFrontier keep) := by
  let cap := un (r.eval (encodeFrontier xs).length)
  have size (x : Word) (hx : x ∈ xs) : x.length ≤ (encodeFrontier xs).length := by
    induction xs with
    | nil => simp at hx
    | cons h hs ih =>
      change x.length ≤ (pairB h (encodeFrontier hs)).length
      rw [pairB_length]
      rcases List.mem_cons.mp hx with rfl | hy
      · omega
      · have hh := ih hy
        omega
  have hcap (x : Word) (hx : x ∈ xs) : (g x).length ≤ cap.length := by
    simpa [cap, un_length] using (hr x).trans (eval_mono r (size x hx))
  have hi := coverIter_spec qs g gs cap xs _ (encodeFrontier_length xs) [] [] [] hcap
  rcases e : retainNew qs [] xs with ⟨seen, keep⟩
  rw [e] at hi
  simp only [List.nil_append, List.append_nil] at hi
  change (unpairB (unpairB (unpairB ((coverStep g)^[(encodeFrontier xs).length]
    (coverState cap xs [] [] []))).2).2).2 = _
  rw [hi]
  simp [coverState, unpairB_pairB, un]

private def queryFrontier (g : Word → Word) (r : Polynomial Nat) (s : Word) : Word :=
  let b := (unpairB s).1
  let d := coverScan g r (unpairB s).2
  let flag := bflag (decide ((unpairB d).1.length ≤ b.length))
  sel flag (pairB [true] []) (pairB [] (unpairB d).2)

private theorem queryFrontier_cpt {g : Word → Word} (hg : CPT g) (r : Polynomial Nat) :
    CPT (queryFrontier g r) := by
  have hscan := cpt_comp cpt_unpairB2 (coverScan_cpt hg r)
  have hcount := cpt_unpairB1_1 hscan
  have hflag := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 hcount) LenCmp.lenLE_polyTime)
  exact bf_cptl (cpt_sel hflag (cpt_const (pairB [true] []))
    (cpt_pairB2 (cpt_const []) (cpt_unpairB2_1 hscan))) (fun _ => rfl)

private theorem queryFrontier_spec (A B : Language Bool) (qs : Word → List Word)
    (g : Word → Word) (r : Polynomial Nat)
    (gs : ∀ x, g x = encodeFrontier (qs x)) (hr : ∀ x, (g x).length ≤ r.eval (List.length x))
    (relation : ∀ x : Word, x ∈ A ↔ ∃ y ∈ qs x, y ∉ B)
    (b : Nat) (xs : List Word)
    (sparse : ∀ z : Finset Word,
      (∀ y ∈ z, y ∈ B ∧ ∃ x ∈ xs, y ∈ qs x) → z.card ≤ b) :
    let out := queryFrontier g r (pairB (un b) (encodeFrontier xs))
    (out = pairB [true] [] ∧ ∃ x ∈ xs, x ∈ A) ∨
      ∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ b ∧
        out = pairB [] (encodeFrontier ys) ∧
        ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  dsimp only
  have he := coverScan_spec qs g r gs hr xs
  have h := retainNew_spec qs [] xs
  rcases e : retainNew qs [] xs with ⟨seen, ys⟩
  rw [e] at he h
  obtain ⟨hsub, hsize, hxs, hys⟩ := h
  have hbound : ys.length ≤ seen.toFinset.card := by simpa using hsize
  by_cases hc : ys.length ≤ b
  · right
    refine ⟨ys, hsub, hc, ?_, ?_⟩
    · simp [queryFrontier, unpairB_pairB, he, un_length, hc, bflag]
    · constructor
      · rintro ⟨x, hx, hxA⟩
        exact ⟨x, hsub.subset hx, hxA⟩
      · rintro ⟨x, hx, hxA⟩
        obtain ⟨y, hy, hyB⟩ := (relation x).mp hxA
        have hm : y ∈ seen := (hxs y).mpr (Or.inr ⟨x,hx,hy⟩)
        rcases (hys y).mp hm with hn | ⟨w, hw, hy⟩
        · contradiction
        · exact ⟨w, hw, (relation w).mpr ⟨y,hy,hyB⟩⟩
  · left
    refine ⟨?_, ?_⟩
    · simp [queryFrontier, unpairB_pairB, he, un_length, hc, bflag]
    · by_contra! hno
      have hcount := sparse seen.toFinset fun y hy => by
        rcases (hxs y).mp (List.mem_toFinset.mp hy) with hn | ⟨w, hw, hy⟩
        · contradiction
        · refine ⟨?_, w, hw, hy⟩
          by_contra hn
          exact hno w hw ((relation w).mpr ⟨y, hy, hn⟩)
      omega

/-- Measured pruning for variable-width lists of conjunctive queries to a sparse target.
For an existential branch, a failed conjunct certifies a true prefix query. -/
theorem CoSparseQueryFrontier (queries : Word → List Word)
    (hf : ComputableInPolyTime (fun x => x) (fun x => x)
      (fun x => (queries x).foldr (fun a b => List.replicate a.length true ++ false :: (a ++ b)) [])) :
    ∃ prune : Word → Word, CPT prune ∧
      ∀ (A B : Language Bool), (∀ x : Word, x ∈ A ↔ ∃ y ∈ queries x, y ∉ B) →
      ∀ (b : Nat) (xs : List Word),
        (∀ z : Finset Word, (∀ y ∈ z, y ∈ B ∧ ∃ x ∈ xs, y ∈ queries x) → z.card ≤ b) →
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        let out := prune (consWord (List.replicate b true) (xs.foldr consWord []))
        (out = consWord [true] [] ∧ ∃ x ∈ xs, x ∈ A) ∨
          ∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ b ∧
            out = consWord [] (ys.foldr consWord []) ∧
            ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  let g := fun x => encodeFrontier (queries x)
  obtain ⟨r, hr⟩ := output_length_poly g hf
  exact ⟨queryFrontier g r, queryFrontier_cpt hf r,
    fun A B hs b xs hsp => queryFrontier_spec A B queries g r (fun _ => rfl) hr hs b xs hsp⟩

end PEqualNP.Outside
