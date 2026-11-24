import PEqualNP.Outside.PolynomialHashWitnessVerifier
import PEqualNP.Outside.CoordinateOptionAlphabet
import PEqualNP.Outside.TaggedRecordProduct
import PEqualNP.Outside.RecordAttachQuery

namespace PEqualNP.Outside.PolynomialHashQueryBatch

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordAttachQuery (attach attach_cpt attach_enc)
open PEqualNP.Outside.TaggedRecordProduct (power power_cpt power_enc words mem_words)
open PEqualNP.Outside.CoordinateOptionAlphabet (alphabet alphabet_cpt alphabet_enc options record_allowed)
open PEqualNP.Outside.PolynomialHashWitnessVerifier (encodeSeed)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

noncomputable def upper (p r : Polynomial ℕ) : Polynomial ℕ :=
  2 * (r*r*(2*p+1)+1)

theorem upper_eval (p r : Polynomial ℕ) (n : ℕ) :
    (upper p r).eval n = 2 * (r.eval n * r.eval n * (2*p.eval n+1)+1) := by
  simp [upper, Polynomial.eval_mul, Polynomial.eval_add]

noncomputable def width (p r : Polynomial ℕ) (x : Word) : Word := un ((upper p r).eval x.length + 1)

theorem width_cpt (p r : Polynomial ℕ) : CPT (width p r) := by
  exact cptl (L055 (upper p r + 1)) (fun x => by
    simp only [width, Polynomial.eval_add, Polynomial.eval_one, un])

noncomputable def produce (p r : Polynomial ℕ) (x : Word) : Word :=
  attach (x, power 3 (alphabet (width p r x)))

theorem produce_cpt (p r : Polynomial ℕ) : CPT (produce p r) := by
  have h := cpt_comp (cpt_comp (width_cpt p r) alphabet_cpt) (power_cpt 3)
  unfold produce
  exact cpt_comp (g := attach) (cpt_pair cpt_id h) attach_cpt

noncomputable def results (p r : Polynomial ℕ) (x : Word) : List Word :=
  (words (options ((upper p r).eval x.length + 1)) 3).map (fun s => pairB x (wire s))

theorem produce_enc (p r : Polynomial ℕ) (x : Word) :
    produce p r x = wire (results p r x) := by
  unfold produce results width
  rw [alphabet_enc, un_length, power_enc, attach_enc, List.map_map]
  rfl

theorem sound (p r : Polynomial ℕ) (x z : Word) (h : z ∈ results p r x) :
    ∃ s : Word, z = pairB x s := by
  obtain ⟨rs, _, rfl⟩ := List.mem_map.mp h
  exact ⟨wire rs,rfl⟩

theorem includes (p r : Polynomial ℕ) (x : Word) (q a b : ℕ)
    (hq : q ≤ (upper p r).eval x.length) (ha : a ≤ (upper p r).eval x.length)
    (hb : b ≤ (upper p r).eval x.length) : pairB x (encodeSeed q a b) ∈ results p r x := by
  let rs := [false :: un q, false :: un a, false :: un b]
  let n := (upper p r).eval x.length + 1
  have hall (j : ℕ) (hj : j < n) : false :: un j ∈ options n :=
    record_allowed n (some (⟨j,hj⟩,false))
  have hm : rs ∈ words (options n) 3 := by
    apply (mem_words _ _ _).mpr
    refine ⟨rfl,?_⟩
    intro z hz
    simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact hall q (Nat.lt_succ_of_le hq)
    · exact hall a (Nat.lt_succ_of_le ha)
    · exact hall b (Nat.lt_succ_of_le hb)
  exact List.mem_map.mpr ⟨rs,hm,rfl⟩

end PEqualNP.Outside.PolynomialHashQueryBatch
