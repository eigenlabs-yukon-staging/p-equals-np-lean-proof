import PEqualNP.Outside.MeasuredBoundedTruthTableBoundary

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Test" => ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
local notation "Table" k => ((Fin k → Bool) → Bool)

private theorem notCpt {f : Word → Bool} (hf : Test f) : Test (fun s => !f s) := by
  have h : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime _ _ _ (fun b => some (!b)) (fun b => by cases b <;> rfl)
  exact cpt_comp hf h

private theorem andCpt {f g : Word → Bool} (hf : Test f) (hg : Test g) :
    Test (fun x => f x && g x) := by
  let B := fun x => sel (bflag (f x)) [] (bflag (g x))
  have hb : CPT B :=
    bf_cptl (cpt_sel (cpt_bitFlag hf) (cpt_const []) (cpt_bitFlag hg)) (fun _ => rfl)
  refine bf_cptl (cpt_comp hb bf_cpt_neL) ?_
  intro x
  cases h : f x <;> cases h' : g x <;> simp [B,h,h',bflag]

private theorem allCpt {α : Type} (xs : List α) (pred : α → Word → Bool)
    (hp : ∀ i, Test (pred i)) :
    Test (fun s => xs.all (fun i => pred i s)) := by
  induction xs with
  | nil =>
    exact bf_cptl (cpt_comp (cpt_const [true]) bf_cpt_neL) (fun _ => rfl)
  | cons a xs ih => exact andCpt (hp a) ih

private theorem sameBoolCpt {f : Word → Bool} (hf : Test f) (b : Bool) :
    Test (fun s => f s == b) := by
  cases b
  · exact bf_cptl (notCpt hf) (fun s => by cases f s <;> rfl)
  · exact bf_cptl hf (fun s => by cases f s <;> rfl)

private noncomputable def tableGroup {k : Nat} (t : Word → Table k) (T : Table k) (x : Word) : Bool :=
  (Finset.univ.toList : List (Fin k → Bool)).all (fun a => t x a == T a)

private theorem tableGroup_cpt {k : Nat} (t : Word → Table k)
    (ht : ∀ a, Test (fun x => t x a)) (T : Table k) : Test (tableGroup t T) :=
  allCpt _ _ (fun a => sameBoolCpt (ht a) (T a))

private theorem tableGroup_spec {k : Nat} (t : Word → Table k) (T : Table k) (x : Word) :
    tableGroup t T x = true ↔ t x = T := by
  simp only [tableGroup, List.all_eq_true, Finset.mem_toList, Finset.mem_univ, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h a => congrFun h a⟩

private noncomputable def thinGroup {k : Nat} (q : Word → Fin k → Word)
    (t : Word → Table k) (T : Table k) (b : Nat) (xs : List Word) : List Word :=
  keepTruthBoundary k b q (xs.filter (tableGroup t T))

private theorem group_compile {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (hq : ∀ i, CPT (fun x => q x i)) (ht : ∀ a, Test (fun x => t x a)) (T : Table k) :
    ∃ run : Word → Word, CPT run ∧
      ∀ (b : Word) (xs : List Word),
        run (pairB b (encodeFrontier xs)) = encodeFrontier (thinGroup q t T b.length xs) := by
  obtain ⟨prune, hp, hs⟩ := compileTruthBoundary k q hq
  let g := fun p : Word × Word => tableGroup t T p.2
  have hg : ComputableInPolyTime encodePair Computability.encodeBool g :=
    cpt_comp (g := tableGroup t T) cpt_snd (tableGroup_cpt t ht T)
  obtain ⟨filterGroup, hf, hfSpec⟩ := FrontierFilterByParameter g hg
  let run := fun s : Word => prune ((unpairB s).1, filterGroup (unpairB s))
  have hc : CPT run :=
    cpt_comp (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB hf)) hp
  refine ⟨run,hc,fun b xs => ?_⟩
  have hh : filterGroup (b, encodeFrontier xs) = encodeFrontier (xs.filter (tableGroup t T)) :=
    hfSpec b xs
  simp only [run, unpairB_pairB, hh, thinGroup]
  exact hs b _

private theorem combine_groups {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (hq : ∀ i, CPT (fun x => q x i)) (ht : ∀ a, Test (fun x => t x a)) (tables : List (Table k)) :
    ∃ allGroups : Word → Word, CPT allGroups ∧
      ∀ (b : Word) (xs : List Word), allGroups (pairB b (encodeFrontier xs)) =
        encodeFrontier (tables.flatMap (fun T => thinGroup q t T b.length xs)) := by
  induction tables with
  | nil => exact ⟨fun _ => [], cpt_const [], fun _ _ => rfl⟩
  | cons T Ts ih =>
    obtain ⟨run, hr, hs⟩ := group_compile q t hq ht T
    obtain ⟨tail, htail, htailSpec⟩ := ih
    exact ⟨fun s => run s ++ tail s, cpt_app2 hr htail, fun b xs => by
      dsimp only
      rw [hs, htailSpec, List.flatMap_cons, encodeFrontier_append_words]⟩

private noncomputable def allTables (k : Nat) : List (Table k) := Finset.univ.toList

private noncomputable def chooseGroups {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (b : Nat) (xs : List Word) : List Word :=
  let group := (allTables k).flatMap (fun T => thinGroup q t T b xs)
  xs.filter (fun x => x ∈ group)

private theorem compileVariableBoundary {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (hq : ∀ i, CPT (fun x => q x i)) (ht : ∀ a, Test (fun x => t x a)) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (b : Word) (xs : List Word),
        run (b, encodeFrontier xs) = encodeFrontier (chooseGroups q t b.length xs) := by
  obtain ⟨group, hg, hgs⟩ := combine_groups q t hq ht (allTables k)
  let pred := fun p : Word × Word => encodedMember p.1 p.2
  have hp : ComputableInPolyTime encodePair Computability.encodeBool pred :=
    cpt_fromRawBool (encodedMember_cpt cpt_unpairB1 cpt_unpairB2)
  obtain ⟨filterOutput, hfo, outSpec⟩ := FrontierFilterByParameter pred hp
  let run := fun p : Word × Word => filterOutput (group (pairB p.1 p.2),p.2)
  have hr : ComputableInPolyTime encodePair (fun x => x) run := by
    refine bf_cptl (cpt_comp cpt_pairB
      (cpt_comp (cpt_pair hg cpt_unpairB2) hfo)) ?_
    rintro ⟨b,xs⟩
    simp [run, unpairB_pairB]
  refine ⟨run, hr, fun b xs => ?_⟩
  let all := (allTables k).flatMap (fun T => thinGroup q t T b.length xs)
  have hh : filterOutput (encodeFrontier all, encodeFrontier xs) =
      encodeFrontier (xs.filter (fun x => encodedMember (encodeFrontier all) x)) :=
    outSpec _ xs
  have he : (fun x : Word => encodedMember (encodeFrontier all) x) =
      (fun x => decide (x ∈ all)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using encodedMember_spec all x
  unfold run
  rw [hgs]
  change filterOutput (encodeFrontier all, encodeFrontier xs) = _
  rw [hh, he]
  rfl

private theorem chooseGroups_length {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (b : Nat) (xs : List Word) (hn : xs.Nodup) :
    (chooseGroups q t b xs).length ≤ (allTables k).length * ttBound b k := by
  let all := (allTables k).flatMap (fun T => thinGroup q t T b xs)
  have hn' : (chooseGroups q t b xs).Nodup := List.Nodup.sublist List.filter_sublist hn
  have hsubset : (chooseGroups q t b xs).toFinset ⊆ all.toFinset := by
    intro x hx
    have hh := (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
    exact List.mem_toFinset.mpr (of_decide_eq_true hh)
  have hc : all.length ≤ (allTables k).length * ttBound b k := by
    have h (tables : List (Table k)) :
        (tables.flatMap (fun T => thinGroup q t T b xs)).length ≤ tables.length * ttBound b k := by
      induction tables with
      | nil => simp
      | cons T rest ih =>
        have hh := (truthBoundarySpec k b q (xs.filter (tableGroup t T))
          (List.Nodup.sublist List.filter_sublist hn)).2.1
        change (thinGroup q t T b xs).length ≤ ttBound b k at hh
        simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
        omega
    exact h (allTables k)
  exact (List.toFinset_card_of_nodup hn').symm.le.trans
    ((Finset.card_le_card hsubset).trans ((List.toFinset_card_le all).trans hc))

private theorem chooseGroups_boundary {k : Nat} (q : Word → Fin k → Word) (t : Word → Table k)
    (b : Nat) (xs : List Word) (hn : xs.Nodup) (S : Finset Word) (hc : S.card ≤ b)
    (x : Word) (h : Boundary (fun y => evalTT q S (t y) y) xs x) :
    x ∈ chooseGroups q t b xs := by
  let T := t x
  let group := xs.filter (tableGroup t T)
  have hx : x ∈ group := List.mem_filter.mpr ⟨h.mem, (tableGroup_spec t T x).mpr rfl⟩
  have hs : group.Sublist xs := List.filter_sublist
  have he := (h.sublist hn hs hx).congr (fun y hy => by
    have ht := (tableGroup_spec t T y).mp (List.mem_filter.mp hy).2
    rw [ht])
  have hh := (truthBoundarySpec k b q group (List.Nodup.sublist hs hn)).2.2 S T x hc he
  apply List.mem_filter.mpr
  exact ⟨h.mem, decide_eq_true (List.mem_flatMap.mpr ⟨T, by simp [allTables], hh⟩)⟩

/-- The measured bounded-width boundary operation permits the truth table to vary
with the candidate when each of its Boolean entries is polynomial-time computable. -/
theorem VariableTruthTableBoundary (k : Nat) (q : Word → Fin k → Word) (t : Word → Table k)
    (hq : ∀ i, CPT (fun x => q x i)) (ht : ∀ a, Test (fun x => t x a)) :
    ∃ (run : Word × Word → Word) (prune : Nat → List Word → List Word) (p : Polynomial Nat),
      ComputableInPolyTime encodePair (fun x => x) run ∧
      (∀ (b : Word) (xs : List Word),
        let enc := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (b, xs.foldr enc []) = (prune b.length xs).foldr enc []) ∧
      ∀ (b : Nat) (xs : List Word), xs.Nodup →
        (prune b xs).Sublist xs ∧ (prune b xs).length ≤ p.eval b ∧
        ∀ (S : Finset Word) (l r : List Word) (x : Word), S.card ≤ b → xs = l ++ x :: r →
          (∀ y ∈ l ++ [x], t y (fun i => decide (q y i ∈ S)) = true) →
          (∀ y ∈ r, t y (fun i => decide (q y i ∈ S)) = false) → x ∈ prune b xs := by
  obtain ⟨run,hr, hs⟩ := compileVariableBoundary q t hq ht
  obtain ⟨p,hp⟩ := truthBoundaryBoundPolynomial k
  refine ⟨run,chooseGroups q t,Polynomial.C (allTables k).length * p,hr,hs,fun b xs hn => ?_⟩
  refine ⟨List.filter_sublist, by simpa [hp] using chooseGroups_length q t b xs hn, ?_⟩
  intro S l r x hb he hg hf
  exact chooseGroups_boundary q t b xs hn S hb x ⟨l,r,he,hg,hf⟩

end PEqualNP.Outside
