import PEqualNP.Outside.AllRecordTest
import PEqualNP.Outside.RecordBlockSplit
import PEqualNP.Outside.SparseBoundedWordIsolation
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.SparsePatternMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordBlockSplit (skip skip_cpt)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.AllRecordTest (check check_cpt check_enc)
open PEqualNP.Outside.SparseCoordinateIsolation (Pattern permits)
open PEqualNP.Outside.SparseBoundedWordIsolation (bits)
open PEqualNP.Outside.UniformWitnessBitEncoding (code)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF cpt_neS)

def recordCode {n : ℕ} : Option (Fin n × Bool) → Word
  | none => []
  | some (i,b) => b :: un i.val

def ask (q : Word × Word) : Bool :=
  !(sel q.1 [true] (bflag (decide ((skip q.1.tail q.2).headD false = q.1.headD false)))).isEmpty

theorem ask_cpt : ComputableInPolyTime encodePair Computability.encodeBool ask := by
  have hreq := cpt_comp cpt_unpairB1 cpt_firstF
  have hobs := cpt_comp (skip_cpt (cpt_tail1 cpt_unpairB1) cpt_unpairB2) cpt_firstF
  have h := cpt_comp (cpt_sel cpt_unpairB1 (cpt_const [true]) (cpt_eqF hobs hreq)) cpt_neS
  exact cptl (cpt_comp cpt_pairB h) (fun q => by
    cases ho : (skip q.1.tail q.2).headD false <;> cases hr : q.1.headD false <;>
      (simp only [ask, unpairB_pairB, ho, hr] <;> simp [bflag]))

private theorem head_drop (w : Word) (i : ℕ) : (w.drop i).headD false = w[i]?.getD false := by
  induction i generalizing w with
  | zero => cases w <;> rfl
  | succ i ih => cases w <;> simp [ih]

theorem ask_enc (b : ℕ) (w : Word) (r : Option (Fin (2*b+1) × Bool)) :
    ask (recordCode r, code (un b) w) = true ↔ r.elim True (fun q => bits b w q.1 = q.2) := by
  cases r with
  | none => simp [ask, recordCode, sel]
  | some r =>
    obtain ⟨i,t⟩ := r
    have he : (skip (un i.val) (code (un b) w)).headD false = bits b w i := by
      rw [skip, un_length, head_drop]
      rfl
    simp only [ask, recordCode, List.tail_cons, List.headD_cons, he, Option.elim_some, sel,
      List.cons_ne_nil, ite_false]
    by_cases hb : bits b w i = t <;> simp [bflag, hb]

def patternCode {n c : ℕ} (p : Pattern n c) : Word :=
  wire (List.ofFn (fun i => recordCode (p i)))

def patternTest (q : Word × Word) : Bool := check ask q

theorem patternTest_cpt : ComputableInPolyTime encodePair Computability.encodeBool patternTest :=
  check_cpt ask ask_cpt

theorem patternTest_enc (b c : ℕ) (p : Pattern (2*b+1) c) (w : Word) :
    patternTest (patternCode p, code (un b) w) = true ↔ permits p (bits b w) := by
  unfold patternTest patternCode permits
  rw [check_enc]
  constructor
  · intro h i
    exact (ask_enc b w (p i)).mp (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro h r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact (ask_enc b w (p i)).mpr (h i)

end PEqualNP.Outside.SparsePatternMachine
