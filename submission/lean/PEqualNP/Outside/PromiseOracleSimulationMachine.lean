import PEqualNP.Outside.QueryListAny
import PEqualNP.Outside.UniformWitnessBitEncoding
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.PromiseOracleSimulationMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.UniformWitnessBitEncoding (fill fill_cpt fill_eq)
open PEqualNP.Outside.QueryListAny (answer answer_cpt answer_enc wire_fold)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)

noncomputable def coinPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.C 2 * p + Polynomial.C 3) * (Polynomial.C 2 * p + Polynomial.C 2)

theorem coinPolynomial_eval (p : Polynomial ℕ) (n : ℕ) :
    (coinPolynomial p).eval n = (2 * p.eval n + 3) * (2 * p.eval n + 2) := by
  simp [coinPolynomial]

noncomputable def correctLength (p : Polynomial ℕ) (q : Word × Word) : Word :=
  bflag (decide (q.2.length = (coinPolynomial p).eval q.1.length))

theorem correctLength_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun w : Word => w) (correctLength p) := by
  have hB := cpt_comp cpt_unpairB2 (fill_cpt true)
  have hE := cpt_comp cpt_unpairB1 (L055 (coinPolynomial p))
  have h := cpt_comp cpt_pairB (cpt_eqF hB hE)
  exact cptl h (fun q => by
    simp only [unpairB_pairB, correctLength, fill_eq, bflag]
    have he : List.replicate q.2.length true =
        List.replicate ((coinPolynomial p).eval q.1.length) true ↔
        q.2.length = (coinPolynomial p).eval q.1.length := by
      constructor
      · intro h
        simpa using congrArg List.length h
      · exact fun h => h ▸ rfl
    simp only [he])

noncomputable def simulate (p : Polynomial ℕ) (G : Word × Word → Word) (O : Word → Bool) (q : Word × Word) : Bool :=
  (sel (correctLength p q) [true] (sel (bflag (answer O (G q))) [true] [])).isEmpty

theorem simulate_cpt (p : Polynomial ℕ) (G : Word × Word → Word) (O : Word → Bool)
    (hG : ComputableInPolyTime encodePair (fun w : Word => w) G)
    (hO : ComputableInPolyTime (fun w : Word => w) Computability.encodeBool O) :
    ComputableInPolyTime encodePair Computability.encodeBool (simulate p G O) := by
  have hlen := cpt_comp cpt_unpairB (correctLength_cpt p)
  have ha := cpt_bitFlag (cpt_comp (cpt_comp cpt_unpairB hG) (answer_cpt O hO))
  have h := cpt_comp (cpt_sel hlen (cpt_const [true]) (cpt_sel ha (cpt_const [true]) (cpt_const []))) cpt_isEmpty
  exact cptl (cpt_comp cpt_pairB h) (fun q => by simp [simulate, unpairB_pairB, bflag])

theorem wrong_length (p : Polynomial ℕ) (G : Word × Word → Word) (O : Word → Bool) (x r : Word)
    (h : r.length ≠ (coinPolynomial p).eval x.length) : simulate p G O (x,r) = false := by
  simp [simulate, correctLength, h, bflag, sel]

theorem correct_length (p : Polynomial ℕ) (G : Word × Word → Word) (O : Word → Bool) (x r : Word)
    (h : r.length = (coinPolynomial p).eval x.length) :
    simulate p G O (x,r) = true ↔ answer O (G (x,r)) = true := by
  cases ha : answer O (G (x,r)) <;> simp [simulate, correctLength, h, ha, bflag, sel]

theorem batch_correct (p : Polynomial ℕ) (G : Word × Word → Word) (O : Word → Bool)
    (x r : Word) (qs : List Word) (hl : r.length = (coinPolynomial p).eval x.length)
    (hq : G (x,r) = qs.foldr (fun y rest => List.replicate y.length true ++ false :: (y ++ rest)) []) :
    simulate p G O (x,r) = true ↔ ∃ q ∈ qs, O q = true := by
  rw [correct_length p G O x r hl, hq, ← wire_fold, answer_enc]

end PEqualNP.Outside.PromiseOracleSimulationMachine
