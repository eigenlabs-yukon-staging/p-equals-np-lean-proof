import PEqualNP.Outside.UniformWitnessBitEncoding
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.UnaryRemainderMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.UniformWitnessBitEncoding (Word fill fill_cpt fill_eq)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (q r a : Word) : Word := pairB q (pairB r a)

def modulus (z : Word) : Word := (unpairB z).1
def remaining (z : Word) : Word := (unpairB (unpairB z).2).1
def residue (z : Word) : Word := (unpairB (unpairB z).2).2

def increment (q a : Word) : Word :=
  sel (bflag (decide (fill true q = fill true (true :: a)))) (true :: a) []

def step (z : Word) : Word :=
  let q := modulus z
  let r := remaining z
  let a := residue z
  sel r z (pack q r.tail (increment q a))

theorem step_cpt : CPT step := by
  have hq : CPT modulus := cpt_unpairB1
  have hr : CPT remaining := cpt_unpairB1_1 cpt_unpairB2
  have ha : CPT residue := cpt_unpairB2_1 cpt_unpairB2
  have hi := cpt_cons1 true ha
  have he := cpt_eqF (cpt_comp hq (fill_cpt true)) (cpt_comp hi (fill_cpt true))
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 hq (cpt_pairB2 (cpt_tail1 hr)
    (cpt_sel he hi (cpt_const []))))) (fun _ => rfl)

theorem step_size (z : Word) : (step z).length ≤ z.length + 3 := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have ht : (remaining z).tail.length ≤ (remaining z).length := by simp [List.length_tail]
  have hi (q a : Word) : (increment q a).length ≤ a.length + 1 := by
    unfold increment sel
    split <;> simp
  have h := hi (modulus z) (residue z)
  simp only [step,sel]
  split
  · omega
  · simp only [pack,pairB_length,modulus,remaining,residue] at *
    omega

def rem (q : Word × Word) : Word := residue (step^[q.2.length] (pack q.1 q.2 []))

theorem rem_cpt : ComputableInPolyTime encodePair (fun x : Word => x) rem := by
  obtain ⟨m⟩ := step_cpt
  have hlo := Iter.iter_polyTime step m 3 step_size
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl (cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))))
      (fun q => by simp [pack, unpairB_pairB])
  have ho : CPT residue := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hs cpt_snd) hlo) ho) (fun _ => rfl)

theorem increment_enc (q : Word) (i : ℕ) (h : q.length = 0 ∨ i < q.length) :
    increment q (un i) = un ((i+1) % q.length) := by
  have he : fill true q = fill true (true :: un i) ↔ q.length = i + 1 := by
    simp only [fill_eq, List.length_cons, un_length]
    constructor
    · intro h
      simpa only [List.length_replicate] using congrArg List.length h
    · exact fun h => h ▸ rfl
  unfold increment
  by_cases hn : q.length = i+1
  · simp [(he.mpr hn), hn, bflag, sel, un]
  · have hne := mt he.mp hn
    simp only [hne, decide_false, bflag, sel, ite_true]
    rcases h with h | h
    · simp [h, un, List.replicate_succ]
    · have hl : i+1 < q.length := by omega
      rw [Nat.mod_eq_of_lt hl]
      rfl

theorem scan (q r : Word) (i : ℕ) (h : q.length = 0 ∨ i < q.length) :
    step^[r.length] (pack q r (un i)) = pack q [] (un ((i + r.length) % q.length)) := by
  induction r generalizing i with
  | nil =>
    have hi : i % q.length = i := by
      rcases h with h | h
      · simp [h]
      · exact Nat.mod_eq_of_lt h
    simp [hi]
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : step (pack q (r :: rs) (un i)) = pack q rs (un ((i+1)%q.length)) := by
      simp [step,pack,modulus,remaining,residue,unpairB_pairB,sel,increment_enc _ _ h]
    rw [hstep, ih _ (by
      by_cases hz : q.length = 0
      · exact Or.inl hz
      · exact Or.inr (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)))]
    rw [Nat.mod_add_mod]
    rw [show i + 1 + rs.length = i + (rs.length + 1) by omega]

theorem rem_enc (q r : Word) : rem (q,r) = un (r.length % q.length) := by
  have hz : q.length = 0 ∨ 0 < q.length := by omega
  have h := scan q r 0 hz
  unfold rem
  change residue (step^[r.length] (pack q r (un 0))) = _
  rw [h]
  simp [residue,pack,unpairB_pairB]

end PEqualNP.Outside.UnaryRemainderMachine
