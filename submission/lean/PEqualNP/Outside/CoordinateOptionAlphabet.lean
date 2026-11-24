import PEqualNP.Outside.SparsePatternMachine
import PEqualNP.Outside.RecordPrefixQueries

namespace PEqualNP.Outside.CoordinateOptionAlphabet

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)
open PEqualNP.Outside.SparsePatternMachine (recordCode)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (c index out : Word) : Word := pairB c (pairB index out)
def clock (z : Word) : Word := (unpairB z).1
def ordinal (z : Word) : Word := (unpairB (unpairB z).2).1
def output (z : Word) : Word := (unpairB (unpairB z).2).2

def step (z : Word) : Word :=
  let c := clock z
  let i := ordinal z
  let name := cut c i
  let more := pairB (false :: name) [] ++ pairB (true :: name) []
  pack c (true :: i) (output z ++ more)

theorem step_cpt : CPT step := by
  have hc : CPT clock := cpt_unpairB1
  have hi : CPT ordinal := cpt_unpairB1_1 cpt_unpairB2
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  have hindex := cut_cpt hc hi
  have hf := cpt_pairB2 (cpt_cons1 false hindex) (cpt_const [])
  have ht := cpt_pairB2 (cpt_cons1 true hindex) (cpt_const [])
  exact cptl (cpt_pairB2 hc (cpt_pairB2 (cpt_cons1 true hi) (cpt_app2 ho (cpt_app2 hf ht))))
    (fun _ => rfl)

def measure (z : Word) : ℕ := 4 * (clock z).length + 10

theorem step_size (z : Word) : (step z).length ≤ z.length + measure z := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have hc : (cut (clock z) (ordinal z)).length ≤ (clock z).length := by
    simp [cut_eq, List.length_take]
  simp only [step, pack, measure, clock, ordinal, output, pairB_length, List.length_append,
    List.length_cons, List.length_nil] at *
  omega

theorem measure_step (z : Word) : measure (step z) ≤ measure z := by
  simp [measure, step, pack, clock, unpairB_pairB]

def alphabet (c : Word) : Word := output (step^[c.length] (pack c [] (wire [[]])))

theorem alphabet_cpt : CPT alphabet := by
  obtain ⟨m⟩ := step_cpt
  have hlo := Iter.iter_polyTime_measure step m measure 14 measure_step step_size (by
    intro z
    have h := unpairB_length z
    unfold measure clock
    omega)
  have hs : CPT (fun c => pack c [] (wire [[]])) :=
    cpt_pairB2 cpt_id (cpt_const (pairB [] (wire [[]])))
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pair hs cpt_id) hlo) ho) (fun _ => rfl)

def after (i : ℕ) : ℕ → List Word
  | 0 => []
  | n + 1 => (false :: un i) :: (true :: un i) :: after (i+1) n

def options (n : ℕ) : List Word := [] :: after 0 n

theorem pair_two (u v : Word) : wire [u,v] = pairB u [] ++ pairB v [] := by
  simp [wire, pairB, List.append_assoc]

theorem step_enc (c : Word) (i : ℕ) (out : List Word) (h : i ≤ c.length) :
    step (pack c (un i) (wire out)) =
      pack c (un (i+1)) (wire (out ++ [false :: un i, true :: un i])) := by
  have hn : (un i).length ≤ c.length := by simpa only [un_length] using h
  simp only [step, pack, clock, ordinal, output, unpairB_pairB, cut_eq, List.take_of_length_le hn,
    wire_append out [false :: un i, true :: un i], pair_two]
  rfl

theorem scan (c : Word) (i n : ℕ) (out : List Word) (h : i+n ≤ c.length) :
    step^[n] (pack c (un i) (wire out)) = pack c (un (i+n)) (wire (out ++ after i n)) := by
  induction n generalizing i out with
  | zero => simp [after]
  | succ n ih =>
    rw [Function.iterate_succ_apply, step_enc c i out (by omega), ih _ _ (by omega)]
    simp [after, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem alphabet_enc (c : Word) : alphabet c = wire (options c.length) := by
  unfold alphabet
  change output (step^[c.length] (pack c (un 0) (wire [[]]))) = _
  rw [scan c 0 c.length [[]] (by simp)]
  simp [options, output, pack, unpairB_pairB]

theorem mem_after (i n j : ℕ) (b : Bool) (hl : i ≤ j) (hr : j < i+n) :
    b :: un j ∈ after i n := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases he : j = i
    · subst j
      cases b <;> simp [after]
    · have hs : i+1 ≤ j := by omega
      have ht : j < (i+1)+n := by omega
      simp only [after, List.mem_cons]
      exact Or.inr (Or.inr (ih _ hs ht))

theorem record_allowed (n : ℕ) (r : Option (Fin n × Bool)) : recordCode r ∈ options n := by
  cases r with
  | none => simp [recordCode, options]
  | some r =>
    exact List.mem_cons_of_mem _ (mem_after 0 n r.1.val r.2 (Nat.zero_le _) (by simpa using r.1.isLt))

end PEqualNP.Outside.CoordinateOptionAlphabet
