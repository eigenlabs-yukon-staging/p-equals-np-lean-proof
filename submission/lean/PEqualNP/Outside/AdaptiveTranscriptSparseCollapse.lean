import PEqualNP.Outside.VariableTruthTableSparseCollapse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool

private def answerAt (d : Nat) (a : Fin (2 ^ (d+1)) → Bool) (history : Word) : Bool :=
  a ⟨idx history % (2 ^ (d+1)), Nat.mod_lt _ (by positivity)⟩

def runSparseTranscript (queryAnswer leaf : Word → Bool) (d : Nat) (history : Word) : Bool :=
  Nat.rec leaf (fun _ run p => run (p ++ [queryAnswer p])) d history

private theorem transcript_polyTime (answers : Word → Bool) (leaf : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool leaf)
    (n : Nat) (p : Word) :
    ComputableInPolyTime (fun x : Word => x) Computability.encodeBool
      (fun x => runSparseTranscript answers (fun h => leaf (x,h)) n p) := by
  induction n generalizing p with
  | zero => exact cpt_comp (cpt_pair cpt_id (cpt_const p)) hc
  | succ n ih => exact ih (p ++ [answers p])

/-- A machine may generate its query from a fixed-length binary answer transcript.
The number of adaptive rounds is a fixed constant. -/
theorem AdaptiveTranscriptSparseCollapse (A B : Language Bool) (hard : NPHard A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (S : Finset Word),
      (∀ y ∈ S, y ∈ B ∧ y.length ≤ n) → S.card ≤ s.eval n)
    (d : Nat) (query : Word × Word → Word) (leaf : Word × Word → Bool)
    (hq : ComputableInPolyTime encodePair (fun x => x) query)
    (hl : ComputableInPolyTime encodePair Computability.encodeBool leaf)
    (correct : ∀ x : Word, x ∈ A ↔ runSparseTranscript
      (fun p => @decide (query (x,p) ∈ B) (Classical.propDecidable _))
      (fun p => leaf (x,p)) d [] = true) :
    P = NP := by
  let k := 2 ^ (d+1)
  let q := fun x (i : Fin k) => query (x,cand i.val)
  have hqc : ∀ i, ComputableInPolyTime (fun x : Word => x) (fun x => x) (fun x => q x i) :=
    fun i => cpt_comp (cpt_pair cpt_id (cpt_const (cand i.val))) hq
  let T := fun x (a : Fin k → Bool) => runSparseTranscript (answerAt d a) (fun p => leaf (x,p)) d []
  refine VariableTruthTableSparseCollapse A B hard s sparse k q hqc T ?_ ?_
  · intro a
    exact transcript_polyTime (answerAt d a) leaf hl d []
  · intro x
    rw [correct]
    let good := fun p => @decide (query (x,p) ∈ B) (Classical.propDecidable _)
    let a := fun i : Fin k => @decide (q x i ∈ B) (Classical.propDecidable _)
    change runSparseTranscript good (fun p => leaf (x,p)) d [] = true ↔
      runSparseTranscript (answerAt d a) (fun p => leaf (x,p)) d [] = true
    have eq (n : Nat) (p : Word) (hp : p.length + n ≤ d) :
        runSparseTranscript good (fun t => leaf (x,t)) n p =
          runSparseTranscript (answerAt d a) (fun t => leaf (x,t)) n p := by
      induction n generalizing p with
      | zero => rfl
      | succ n ih =>
        have hidx := idx_lt_of_length_le (s := p) (b := d) (by omega)
        have hi : idx p < 2 ^ (d+1) := by omega
        have ha : answerAt d a p = good p := by
          simp [answerAt, a, q, Nat.mod_eq_of_lt hi, cand_idx, good]
        simp only [runSparseTranscript, ha]
        exact ih _ (by simp; omega)
    rw [eq d [] (by simp)]

end PEqualNP.Outside
