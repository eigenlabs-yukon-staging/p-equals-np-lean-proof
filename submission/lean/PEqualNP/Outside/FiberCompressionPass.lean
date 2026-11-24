import PEqualNP.Outside.FrontierFilterByParameter
import PEqualNP.Library.Machines.IterMeasure

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def sameKey (key : Word → Word) (p : Word × Word) : Bool :=
  decide (key p.2 = p.1)

private theorem sameKey_cpt {key : Word → Word} (hk : CPT key) :
    ComputableInPolyTime encodePair Computability.encodeBool (sameKey key) := by
  have hh := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF (cpt_comp cpt_unpairB2 hk) cpt_unpairB1
  apply cpt_fromRawBool
  refine bf_cptl (cpt_comp hh bf_cpt_neL) ?_
  intro s
  by_cases h : key (unpairB s).2 = (unpairB s).1 <;> simp [sameKey, h, bflag]

private def mergeKey (key : Word → Word) (p : Word × Word) : Bool :=
  let a := unpairB p.1
  !(sameKey key (a.1,p.2)) || encodedMember a.2 p.2

private theorem mergeKey_cpt {key : Word → Word} (hk : CPT key) :
    ComputableInPolyTime encodePair Computability.encodeBool (mergeKey key) := by
  have hkey := cpt_unpairB1_1 cpt_unpairB1
  have hkept := cpt_unpairB2_1 cpt_unpairB1
  have hsame := cpt_bitFlag (cpt_comp (cpt_pair hkey cpt_unpairB2) (sameKey_cpt hk))
  have hmember := cpt_bitFlag (encodedMember_cpt hkept cpt_unpairB2)
  apply cpt_fromRawBool
  refine bf_cptl (cpt_comp (cpt_sel hsame (cpt_const [true]) hmember) bf_cpt_neL) ?_
  intro s
  unfold mergeKey
  cases h₁ : sameKey key ((unpairB (unpairB s).1).1,(unpairB s).2) <;>
    cases h₂ : encodedMember (unpairB (unpairB s).1).2 (unpairB s).2 <;> simp [h₁,h₂,bflag]

def compressOneFiber (key : Word → Word) (thin : Nat → List Word → List Word)
    (b : Nat) (pivot : Word) (xs : List Word) : List Word :=
  let fiber := xs.filter (fun y => key y == key pivot)
  let chosen := thin b fiber
  xs.filter (fun y => key y != key pivot || y ∈ chosen)

private theorem compressOneFiber_sublist (key : Word → Word)
    (thin : Nat → List Word → List Word) (b : Nat) (pivot : Word) (xs : List Word) :
    (compressOneFiber key thin b pivot xs).Sublist xs :=
  List.filter_sublist

private theorem encoded_sublist_size {xs ys : List Word} (hs : ys.Sublist xs) :
    (encodeFrontier ys).length ≤ (encodeFrontier xs).length := by
  induction hs with
  | slnil => rfl
  | cons x h ih =>
    change (encodeFrontier _).length ≤ (pairB x (encodeFrontier _)).length
    rw [pairB_length]
    omega
  | cons_cons x h ih =>
    change (pairB x (encodeFrontier _)).length ≤ (pairB x (encodeFrontier _)).length
    simp only [pairB_length]
    omega

private theorem mergeKey_spec (key : Word → Word) (a y : Word) (chosen : List Word) :
    mergeKey key (pairB a (encodeFrontier chosen), y) =
      (key y != a || y ∈ chosen) := by
  have he := encodedMember_spec chosen y
  have hh : encodedMember (encodeFrontier chosen) y = decide (y ∈ chosen) := by
    cases h : encodedMember (encodeFrontier chosen) y <;> cases d : decide (y ∈ chosen)
    · rfl
    · exfalso
      have ht := he.mpr (of_decide_eq_true d)
      rw [h] at ht
      contradiction
    · exfalso
      have ht := decide_eq_true (he.mp h)
      rw [d] at ht
      contradiction
    · rfl
  have beq : (key y == a) = decide (key y = a) := by
    apply Bool.eq_iff_iff.mpr
    simp
  change mergeKey key (pairB a (encodeFrontier chosen), y) =
    (!(key y == a) || decide (y ∈ chosen))
  simp [mergeKey, sameKey, unpairB_pairB, hh, beq]

private theorem singleFiberMachine (key : Word → Word) (hk : CPT key)
    (thin : Nat → List Word → List Word)
    (p : Word × Word → Word) (hp : ComputableInPolyTime encodePair (fun x => x) p)
    (hspec : ∀ (b : Word) (xs : List Word),
      p (b,encodeFrontier xs) = encodeFrontier (thin b.length xs)) :
    ∃ single : Word → Word, CPT single ∧
      ∀ (b : Word) (pivot : Word) (xs : List Word),
        single (pairB b (pairB pivot (encodeFrontier xs))) =
          encodeFrontier (compressOneFiber key thin b.length pivot xs) := by
  obtain ⟨extract, he, extractSpec⟩ := FrontierFilterByParameter (sameKey key) (sameKey_cpt hk)
  obtain ⟨merge, hm, mergeSpec⟩ := FrontierFilterByParameter (mergeKey key) (mergeKey_cpt hk)
  let single := fun s : Word =>
    let b := (unpairB s).1
    let pivot := (unpairB (unpairB s).2).1
    let xs := (unpairB (unpairB s).2).2
    let a := key pivot
    let chosen := p (b,extract (a,xs))
    merge (pairB a chosen,xs)
  have hb := cpt_unpairB1
  have hraw := cpt_unpairB2
  have ha := cpt_comp (cpt_unpairB1_1 hraw) hk
  have hxs := cpt_unpairB2_1 hraw
  have hchoose := cpt_comp (cpt_pair hb (cpt_comp (cpt_pair ha hxs) he)) hp
  have hc : CPT single := cpt_comp (cpt_pair (cpt_pairB2 ha hchoose) hxs) hm
  refine ⟨single,hc,fun b pivot xs => ?_⟩
  let fiber := xs.filter (fun y => key y == key pivot)
  have hExtract : extract (key pivot,encodeFrontier xs) = encodeFrontier fiber := by
    have he := extractSpec (key pivot) xs
    change extract (key pivot,encodeFrontier xs) =
      encodeFrontier (xs.filter (fun x => sameKey key (key pivot,x))) at he
    rw [he]
    congr 1
    apply congrArg (fun pred => xs.filter pred)
    funext y
    apply Bool.eq_iff_iff.mpr
    simp [sameKey]
  let chosen := thin b.length fiber
  have hMerge :
      merge (pairB (key pivot) (encodeFrontier chosen),encodeFrontier xs) =
        encodeFrontier (compressOneFiber key thin b.length pivot xs) := by
    refine (mergeSpec (pairB (key pivot) (encodeFrontier chosen)) xs).trans ?_
    change encodeFrontier (xs.filter
      (fun y => mergeKey key (pairB (key pivot) (encodeFrontier chosen), y))) = _
    simp [mergeKey_spec, compressOneFiber, fiber, chosen]
  simpa [single, unpairB_pairB, hExtract, hspec, chosen] using hMerge

private def passStep (single : Word → Word) (s : Word) : Word :=
  let cap := (unpairB s).1
  let r₀ := (unpairB s).2
  let b := (unpairB r₀).1
  let r₁ := (unpairB r₀).2
  let todo := (unpairB r₁).1
  let xs := (unpairB r₁).2
  let repl := single (pairB b (pairB (unpairB todo).1 xs))
  let ok := bflag (decide (repl.length ≤ cap.length))
  sel todo s (pairB cap (pairB b (pairB (unpairB todo).2 (sel ok xs repl))))

private def passMeasure (s : Word) : Nat := (unpairB s).1.length + 3

private theorem passMeasure_step (single : Word → Word) (s : Word) :
    passMeasure (passStep single s) ≤ passMeasure s := by
  unfold passStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [passMeasure, unpairB_pairB]

private theorem passStep_size (single : Word → Word) (s : Word) :
    (passStep single s).length ≤ s.length + passMeasure s := by
  have h₀ := unpairB_length s
  have h₁ := unpairB_length (unpairB s).2
  have h₂ := unpairB_length (unpairB (unpairB s).2).2
  have ht := unpairB_length (unpairB (unpairB (unpairB s).2).2).1
  unfold passStep passMeasure
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length]
    split
    · omega
    · rename_i hn
      have hc := (not_congr (bflag_eq_nil _)).mp hn
      simp only [Bool.not_eq_false, decide_eq_true_eq] at hc
      omega

private theorem passStep_cpt {single : Word → Word} (hs : CPT single) : CPT (passStep single) := by
  have hc := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have h₀ := cpt_unpairB2_1 cpt_unpairB2
  have ht := cpt_unpairB1_1 h₀
  have hx := cpt_unpairB2_1 h₀
  have hr := cpt_comp (cpt_pairB2 hb (cpt_pairB2 (cpt_unpairB1_1 ht) hx)) hs
  have hcmp := cpt_bitFlag (cpt_comp (cpt_pair hc hr) LenCmp.lenLE_polyTime)
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hc (cpt_pairB2 hb
    (cpt_pairB2 (cpt_unpairB2_1 ht) (cpt_sel hcmp hx hr))))) (fun _ => rfl)

private def passState (cap b : Word) (todo xs : List Word) : Word :=
  pairB cap (pairB b (pairB (encodeFrontier todo) (encodeFrontier xs)))

private theorem passRun (single : Word → Word) (key : Word → Word)
    (thin : Nat → List Word → List Word)
    (h : ∀ (b : Word) (pivot : Word) (xs : List Word),
      single (pairB b (pairB pivot (encodeFrontier xs))) =
        encodeFrontier (compressOneFiber key thin b.length pivot xs))
    (cap b : Word) (todo : List Word) :
    ∀ (k : Nat), todo.length ≤ k → ∀ xs : List Word,
      (encodeFrontier xs).length ≤ cap.length →
      (passStep single)^[k] (passState cap b todo xs) =
        passState cap b [] (todo.foldl (fun ys pivot => compressOneFiber key thin b.length pivot ys) xs) := by
  induction todo with
  | nil =>
    intro k _ xs _
    have hf : passStep single (passState cap b [] xs) = passState cap b [] xs := by
      simp [passStep, passState, encodeFrontier, unpairB_pairB]
    exact Function.iterate_fixed hf k
  | cons x todo ih =>
    intro k hk xs hcap
    cases k with
    | zero => simp at hk
    | succ k =>
      let ys := compressOneFiber key thin b.length x xs
      have hp : (encodeFrontier ys).length ≤ cap.length :=
        (encoded_sublist_size (compressOneFiber_sublist key thin b.length x xs)).trans hcap
      have hstep : passStep single (passState cap b (x::todo) xs) =
          passState cap b todo ys := by
        have hne : pairB x (encodeFrontier todo) ≠ [] := encodeFrontier_cons_ne x todo
        change passStep single (pairB cap (pairB b (pairB (pairB x (encodeFrontier todo))
          (encodeFrontier xs)))) = _
        have he : single (pairB b (pairB x (encodeFrontier xs))) = encodeFrontier ys := h b x xs
        simp [passStep, passState, unpairB_pairB, sel, hne, bflag, he, hp]
      rw [Function.iterate_succ_apply, hstep, ih k (by simpa using hk) ys hp]
      rfl

private def passRaw (single : Word → Word) (s : Word) : Word :=
  let cap := un s.length
  let init := pairB cap s
  (unpairB (unpairB (unpairB ((passStep single)^[s.length] init)).2).2).2

private theorem passRaw_cpt {single : Word → Word} (hs : CPT single) : CPT (passRaw single) := by
  obtain ⟨c⟩ := passStep_cpt hs
  have hg := Iter.iter_polyTime_measure (passStep single) c passMeasure 3
    (passMeasure_step single) (passStep_size single) (fun s => by
      have h := unpairB_length s
      unfold passMeasure
      omega)
  have hc := cpt_pairB2 (L055 Polynomial.X) cpt_id
  have h := cpt_comp (cpt_pair hc cpt_id) hg
  exact bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 h)))
    (fun x => by simp [passRaw, un])

theorem FiberCompressionPass (key : Word → Word) (hk : CPT key)
    (thin : Nat → List Word → List Word)
    (p : Word × Word → Word) (hp : ComputableInPolyTime encodePair (fun x => x) p)
    (hspec : ∀ (b : Word) (xs : List Word),
      let enc := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
      p (b, xs.foldr enc []) = (thin b.length xs).foldr enc []) :
    ∃ run : Word → Word, CPT run ∧
      ∀ (b : Word) (todo xs : List Word),
        let enc := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        let compact := fun ys pivot =>
          let fiber := ys.filter (fun y => key y == key pivot)
          let chosen := thin b.length fiber
          ys.filter (fun y => key y != key pivot || y ∈ chosen)
        run (enc b (enc (todo.foldr enc []) (xs.foldr enc []))) =
          (todo.foldl compact xs).foldr enc [] := by
  obtain ⟨single, hc, hs⟩ := singleFiberMachine key hk thin p hp hspec
  refine ⟨passRaw single, passRaw_cpt hc, fun b todo xs => ?_⟩
  let s := pairB b (pairB (encodeFrontier todo) (encodeFrontier xs))
  have hlen : todo.length ≤ s.length := by
    have := encodeFrontier_length todo
    simp only [s, pairB_length]
    omega
  have hcap : (encodeFrontier xs).length ≤ (un s.length).length := by
    simp only [un_length, s, pairB_length]
    omega
  have he := passRun single key thin hs (un s.length) b todo s.length hlen xs hcap
  change passRaw single s = encodeFrontier
    (todo.foldl (fun ys pivot => compressOneFiber key thin b.length pivot ys) xs)
  unfold passRaw
  change (unpairB (unpairB (unpairB ((passStep single)^[s.length]
    (passState (un s.length) b todo xs))).2).2).2 = _
  rw [he]
  simp [passState, unpairB_pairB]

end PEqualNP.Outside
