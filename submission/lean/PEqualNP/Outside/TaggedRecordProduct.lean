import PEqualNP.Outside.RecordPrefixQueries

namespace PEqualNP.Outside.TaggedRecordProduct

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def tagStep (b : Bool) (z : Word) : Word :=
  let r := (unpairB z).1
  let out := (unpairB z).2
  let item := unpairB r
  sel r z (pairB item.2 (out ++ pairB (b :: item.1) []))

theorem tagStep_cpt (b : Bool) : CPT (tagStep b) := by
  have hr := cpt_unpairB1
  have hh := cpt_unpairB1_1 hr
  have ht := cpt_unpairB2_1 hr
  have ho := cpt_app2 cpt_unpairB2 (cpt_pairB2 (cpt_cons1 b hh) (cpt_const []))
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 ht ho)) (fun _ => rfl)

theorem tagStep_size (b : Bool) (z : Word) : (tagStep b z).length ≤ z.length + 4 := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).1
  simp only [tagStep, sel]
  split
  · omega
  · simp only [pairB_length,List.length_append,List.length_cons,List.length_nil]
    omega

def tagMap (b : Bool) (w : Word) : Word := (unpairB ((tagStep b)^[w.length] (pairB w []))).2

theorem tagMap_cpt (b : Bool) : CPT (tagMap b) := by
  obtain ⟨m⟩ := tagStep_cpt b
  have hr := Iter.iter_polyTime (tagStep b) m 4 (tagStep_size b)
  exact cptl (cpt_comp (cpt_comp (cpt_pair (cpt_pairB2 cpt_id (cpt_const [])) cpt_id) hr)
    cpt_unpairB2) (fun _ => rfl)

theorem tagScan (b : Bool) (rs out : List Word) :
    (tagStep b)^[rs.length] (pairB (wire rs) (wire out)) =
      pairB [] (wire (out ++ rs.map (b :: ·))) := by
  induction rs generalizing out with
  | nil => simp [wire]
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hn : pairB r (wire rs) ≠ [] := by simp [pairB]
    have hs : tagStep b (pairB (wire (r :: rs)) (wire out)) =
        pairB (wire rs) (wire (out ++ [b :: r])) := by
      simp [tagStep, wire, hn, sel, unpairB_pairB, wire_append]
    rw [hs, ih]
    simp [List.append_assoc]

theorem tagMap_enc (b : Bool) (rs : List Word) : tagMap b (wire rs) = wire (rs.map (b :: ·)) := by
  have hl := wire_len rs
  have hh : tagStep b (pairB [] (wire (rs.map (b :: ·)))) = pairB [] (wire (rs.map (b :: ·))) := by
    simp [tagStep, sel, unpairB_pairB]
  have hs := tagScan b rs []
  simp only [wire, List.nil_append] at hs
  unfold tagMap
  rw [← Nat.sub_add_cancel hl, Function.iterate_add_apply, hs, Function.iterate_fixed hh, unpairB_pairB]

def emit (q : Word × Word) : Word :=
  sel (bflag (q.1.headD false))
    (sel (bflag (q.2.headD false)) [] (pairB (pairB q.2.tail q.1.tail) [])) []

theorem emit_cpt : ComputableInPolyTime encodePair (fun x : Word => x) emit := by
  have ha := cpt_unpairB1
  have hb := cpt_unpairB2
  have hA := cpt_comp ha cpt_firstF
  have hB := cpt_comp hb cpt_firstF
  have hpair := cpt_pairB2 (cpt_pairB2 (cpt_tail1 hb) (cpt_tail1 ha)) (cpt_const [])
  have h := cpt_comp cpt_pairB
    (cpt_sel hA (cpt_sel hB (cpt_const []) hpair) (cpt_const []))
  exact cptl h (fun q => by simp [emit, bflag, unpairB_pairB])

theorem emit_size (a b : Word) : (emit (a,b)).length ≤ 4 * a.length + 4 * b.length + 3 := by
  have ha : a.tail.length ≤ a.length := by simp [List.length_tail]
  have hb : b.tail.length ≤ b.length := by simp [List.length_tail]
  unfold emit sel
  split
  · split
    · simp
    · simp only [pairB_length,List.length_nil]
      omega
  · simp

def cross (q : Word × Word) : Word :=
  RecordPairScan.compile emit (tagMap false q.1 ++ tagMap true q.2)

theorem cross_cpt : ComputableInPolyTime encodePair (fun x : Word => x) cross := by
  have h := cpt_comp (cpt_pairG (cpt_comp cpt_fst (tagMap_cpt false)) (cpt_comp cpt_snd (tagMap_cpt true))) cpt_append
  unfold cross
  exact cpt_comp (g := RecordPairScan.compile emit) h (RecordPairScan.compile_cpt emit emit_cpt 4 3 emit_size)

theorem wire_flat (xs : List Word) : wire xs = xs.flatMap (fun a => pairB a []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [wire, pairB, ih, List.append_assoc]

theorem cross_enc (xs ys : List Word) :
    cross (wire xs, wire ys) = wire (xs.flatMap (fun a => ys.map (fun b => pairB b a))) := by
  unfold cross
  rw [tagMap_enc, tagMap_enc, ← wire_append, RecordPairScan.compile_enc, wire_flat]
  simp only [List.flatMap_append, List.flatMap_map, Function.comp_def]
  have he (r : List Word) : r.flatMap (fun _ => ([] : Word)) = [] := by
    induction r with
    | nil => rfl
    | cons a r ih => simp [ih]
  simp [emit, sel, bflag, List.flatMap_assoc, List.flatMap_map, Function.comp_def, he]

def power (c : ℕ) (alphabet : Word) : Word :=
  match c with
  | 0 => wire [[]]
  | c + 1 => cross (power c alphabet, alphabet)

theorem power_cpt (c : ℕ) : CPT (power c) := by
  induction c with
  | zero => exact cpt_const _
  | succ c ih =>
    exact cptl (cpt_comp (cpt_pair ih cpt_id) cross_cpt) (fun a => rfl)

def words (A : List Word) : ℕ → List (List Word)
  | 0 => [[]]
  | c+1 => (words A c).flatMap (fun w => A.map (fun a => a :: w))

theorem power_enc (A : List Word) (c : ℕ) : power c (wire A) = wire ((words A c).map wire) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [power, ih, cross_enc]
    simp [words, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, wire]

theorem mem_words (A : List Word) (c : ℕ) (w : List Word) :
    w ∈ words A c ↔ w.length = c ∧ ∀ a ∈ w, a ∈ A := by
  induction c generalizing w with
  | zero => cases w <;> simp [words]
  | succ c ih =>
    constructor
    · intro hw
      obtain ⟨v,hv,h⟩ := List.mem_flatMap.mp hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      have hs := (ih v).mp hv
      refine ⟨by simp [hs.1], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hs.2 b hb
    · rintro ⟨hlen, hs⟩
      cases w with
      | nil => simp at hlen
      | cons a v =>
        have h : v.length = c := by simpa using hlen
        have hmem := (ih v).mpr ⟨h, fun b hb => hs b (by simp [hb])⟩
        exact List.mem_flatMap.mpr ⟨v,hmem,List.mem_map.mpr ⟨a,hs a (by simp),rfl⟩⟩

end PEqualNP.Outside.TaggedRecordProduct
