import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private def front (s : List Bool) : Bool := s.headD false

private def fillBits : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | false :: mask, word, seed => front word :: fillBits mask word.tail seed
  | true :: mask, word, seed => front seed :: fillBits mask word.tail seed.tail

private def fillStep (s : List Bool) : List Bool :=
  let mask := (unpairB s).1
  let body := (unpairB s).2
  let word := (unpairB body).1
  let cursor := (unpairB body).2
  let seed := (unpairB cursor).1
  let out := (unpairB cursor).2
  if front mask then pairB mask.tail (pairB word.tail
    (pairB seed.tail (out ++ [front seed])))
  else pairB mask.tail (pairB word.tail (pairB seed (out ++ [front word])))

private theorem cpt_front {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => [front (f s)]) := by
  refine cptE (cpt_sel (cpt_hd1 hf) (cpt_const [false]) (cpt_const [true])) (fun s => ?_)
  cases h : f s with
  | nil => rfl
  | cons b bs => cases b <;> simp [sel, hd, front]

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) fillStep := by
  have hmask := cpt_unpairB1
  have hbody := cpt_unpairB2
  have hword := cpt_unpairB1_1 hbody
  have hcursor := cpt_unpairB2_1 hbody
  have hseed := cpt_unpairB1_1 hcursor
  have hout := cpt_unpairB2_1 hcursor
  have hfixed := cpt_pairB2 hseed (cpt_app2 hout (cpt_front hword))
  have hwild := cpt_pairB2 (cpt_tail1 hseed) (cpt_app2 hout (cpt_front hseed))
  have hreturn := cpt_pairB2 (cpt_tail1 hmask)
    (cpt_pairB2 (cpt_tail1 hword) (cpt_sel (cpt_hd1 hmask) hfixed hwild))
  refine cptE hreturn (fun s => ?_)
  unfold fillStep
  cases h : (unpairB s).1 with
  | nil => simp [sel, hd, front]
  | cons b bs => cases b <;> simp [sel, hd, front]

private theorem fillStep_length (s : List Bool) : (fillStep s).length ≤ s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have ht (w : List Bool) : w.tail.length ≤ w.length := by simp
  have hm := ht (unpairB s).1
  have hw := ht (unpairB (unpairB s).2).1
  have hseed := ht (unpairB (unpairB (unpairB s).2).2).1
  dsimp only [fillStep]
  split <;> simp only [pairB_length, List.length_append, List.length_singleton] <;> omega

private theorem run_fill (mask word seed out : List Bool) :
    (unpairB (unpairB (unpairB (fillStep^[mask.length]
      (pairB mask (pairB word (pairB seed out))))).2).2).2 =
      out ++ fillBits mask word seed := by
  induction mask generalizing word seed out with
  | nil => simp [unpairB_pairB, fillBits]
  | cons b mask ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      cases b <;> simp only [fillStep, unpairB_pairB, front, List.headD_cons, List.tail_cons,
        Bool.false_eq_true, ite_false, ite_true]
      · rw [ih, fillBits, List.append_assoc]
        rfl
      · rw [ih, fillBits, List.append_assoc]
        rfl

private theorem fillBits_indexed (mask word seed : List Bool) :
    fillBits mask word seed = (List.range mask.length).map (fun i =>
      if mask.getD i false then seed.getD ((mask.take i).count true) false else word.getD i false) := by
  induction mask generalizing word seed with
  | nil => simp [fillBits]
  | cons b mask ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      cases b <;> simp [fillBits, front, List.head?_eq_getElem?, ih, Function.comp_def, List.getD, List.getElem?_tail]


/-- A measured filler copies fixed positions and consumes one seed bit at each marked position. -/
theorem MeasuredMaskedFill :
    ∃ fill : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) fill ∧
      ∀ mask word seed : List Bool,
        fill (List.replicate mask.length true ++ false :: (mask ++ word), seed) =
          (List.range mask.length).map (fun i =>
            if mask.getD i false then seed.getD ((mask.take i).count true) false else word.getD i false) := by
  let initial := fun s =>
    pairB (unpairB (unpairB s).1).1
      (pairB (unpairB (unpairB s).1).2 (pairB (unpairB s).2 []))
  let raw := fun s => (unpairB (unpairB (unpairB
    (fillStep^[(unpairB (unpairB s).1).1.length] (initial s))).2).2).2
  have hm := cpt_unpairB1_1 cpt_unpairB1
  have hw := cpt_unpairB2_1 cpt_unpairB1
  have hi := cpt_pairB2 hm (cpt_pairB2 hw (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow cpt_step 4 fillStep_length hm hi)))
  refine ⟨fun p => raw (pairB p.1 p.2), cpt_comp cpt_pairB hraw, fun mask word seed => ?_⟩
  change raw (pairB (pairB mask word) seed) = _
  simp only [raw, initial, unpairB_pairB]
  rw [run_fill, List.nil_append]
  exact fillBits_indexed mask word seed

/-- Fixed positions determine the output exactly when the marked positions receive their seed. -/
theorem maskedSeed_exists (mask word target : List Bool)
    (hlen : target.length = mask.length)
    (hagree : ∀ i < mask.length, mask.getD i false = false → target.getD i false = word.getD i false) :
    ∃ seed : List Bool, seed.length = mask.count true ∧
      (List.range mask.length).map (fun i =>
        if mask.getD i false then seed.getD ((mask.take i).count true) false else word.getD i false) = target := by
  have htail (l : List Bool) (i : ℕ) : l.tail.getD i false = l.getD (i + 1) false := by
    simp [List.getD, List.getElem?_tail]
  simp only [← fillBits_indexed]
  induction mask generalizing word target with
  | nil =>
      have ht : target = [] := List.length_eq_zero_iff.mp hlen
      subst target
      exact ⟨[], rfl, rfl⟩
  | cons b mask ih =>
      cases target with
      | nil => simp at hlen
      | cons t target =>
          have ht : target.length = mask.length := by simpa using hlen
          have hp : ∀ i < mask.length, mask.getD i false = false →
              target.getD i false = word.tail.getD i false := by
            intro i hi hb
            simpa [htail] using hagree (i + 1) (by simp; omega) (by simpa using hb)
          obtain ⟨seed, hseed, hcalc⟩ := ih word.tail target ht hp
          cases b with
          | false =>
              have hw : t = front word := by
                simpa [front, List.head?_eq_getElem?] using hagree 0 (by simp) (by simp)
              exact ⟨seed, by simpa using hseed, by simp [fillBits, ← hw, hcalc]⟩
          | true =>
              exact ⟨t :: seed, by simp [hseed], by simp [fillBits, front, hcalc]⟩

end PEqualNP.Outside
