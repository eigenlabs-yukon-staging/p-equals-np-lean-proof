import PEqualNP.Outside.CoordinateOptionAlphabet
import PEqualNP.Outside.TaggedRecordProduct
import PEqualNP.Outside.RecordAttachQuery

namespace PEqualNP.Outside.SparsePatternQueryBatch

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordAttachQuery (attach attach_cpt attach_enc)
open PEqualNP.Outside.TaggedRecordProduct (power power_cpt power_enc words mem_words)
open PEqualNP.Outside.CoordinateOptionAlphabet (alphabet alphabet_cpt alphabet_enc options record_allowed)
open PEqualNP.Outside.SparseCoordinateIsolation (Pattern)
open PEqualNP.Outside.SparsePatternMachine (recordCode patternCode)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def width (p : Polynomial ℕ) (x : Word) : Word := true :: (un (p.eval x.length) ++ un (p.eval x.length))

theorem width_cpt (p : Polynomial ℕ) : CPT (width p) :=
  cpt_cons1 true (cpt_app2 (L055 p) (L055 p))

theorem width_length (p : Polynomial ℕ) (x : Word) :
    (width p x).length = 2 * p.eval x.length + 1 := by
  simp only [width, List.length_cons, List.length_append, un_length]
  omega

def produce (p : Polynomial ℕ) (c : ℕ) (x : Word) : Word :=
  attach (x, power c (alphabet (width p x)))

theorem produce_cpt (p : Polynomial ℕ) (c : ℕ) : CPT (produce p c) := by
  have h := cpt_comp (cpt_comp (width_cpt p) alphabet_cpt) (power_cpt c)
  unfold produce
  exact cpt_comp (g := attach) (cpt_pair cpt_id h) attach_cpt

def results (p : Polynomial ℕ) (c : ℕ) (x : Word) : List Word :=
  (words (options (2 * p.eval x.length + 1)) c).map (fun s => pairB x (wire s))

theorem produce_enc (p : Polynomial ℕ) (c : ℕ) (x : Word) :
    produce p c x = wire (results p c x) := by
  unfold produce results
  rw [alphabet_enc, width_length, power_enc, attach_enc, List.map_map]
  rfl

theorem sound (p : Polynomial ℕ) (c : ℕ) (x z : Word) (h : z ∈ results p c x) :
    ∃ s : Word, z = pairB x s := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
  exact ⟨wire r,rfl⟩

theorem includes (p : Polynomial ℕ) (c : ℕ) (x : Word)
    (f : Pattern (2 * p.eval x.length + 1) c) :
    pairB x (patternCode f) ∈ results p c x := by
  let rs := List.ofFn (fun i => recordCode (f i))
  have hm : rs ∈ words (options (2 * p.eval x.length + 1)) c := by
    apply (mem_words _ _ _).mpr
    refine ⟨List.length_ofFn,?_⟩
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact record_allowed _ (f i)
  exact List.mem_map.mpr ⟨rs,hm,rfl⟩

end PEqualNP.Outside.SparsePatternQueryBatch
