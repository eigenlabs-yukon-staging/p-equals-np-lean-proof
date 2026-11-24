import PEqualNP.Outside.OrderedSparseFrontierSolver
import PEqualNP.Outside.FrontierFilterByParameter
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open TruthTableSolver

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)
local notation "Verifier" => Word × Word → Bool
local notation "ltBit" => (fun u v : Bool => !u && v)

private def allowed (prior w : Word) : Bool :=
  prior.isEmpty || prior.tail.lex w ltBit

private theorem allowed_spec (prior w : Word) :
    allowed prior w = true ↔ prior = [] ∨ prior.tail < w := by
  have h : ltBit = (fun u v : Bool => decide (u < v)) := by
    funext u v
    cases u <;> cases v <;> rfl
  simp [allowed,h]

private def certificateState (x prior rest : Word) : Word :=
  pairB [true] (pairB x (pairB prior rest))

private def certificateStep (v : Verifier) (s : Word) : Word :=
  let active := (unpairB s).1
  let input := (unpairB (unpairB s).2).1
  let inner := (unpairB (unpairB s).2).2
  let prior := (unpairB inner).1
  let rest := (unpairB inner).2
  let q := unpairB rest
  let step := certificateState input (true::q.1) q.2
  sel active [] (sel rest [] (sel (bflag (allowed prior q.1)) []
    (sel (bflag (v (input,q.1))) [] step)))

private theorem certificateStep_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    CPT (certificateStep v) := by
  have hinner := cpt_unpairB2_1 cpt_unpairB2
  have hprior := cpt_unpairB1_1 hinner
  have hrest := cpt_unpairB2_1 hinner
  have hx := cpt_unpairB1_1 cpt_unpairB2
  have hw := cpt_unpairB1_1 hrest
  have ht := cpt_unpairB2_1 hrest
  have hv' := cpt_bitFlag (cpt_comp (cpt_pair hx hw) hv)
  have hlt := cpt_bitFlag (cpt_comp (cpt_pair (cpt_tail1 hprior) hw) LexicographicWordCompare)
  have hall := cpt_sel hprior (cpt_const [true]) hlt
  have hout := cpt_pairB2 (cpt_const [true]) (cpt_pairB2 hx (cpt_pairB2 (cpt_cons1 true hw) ht))
  have h := cpt_sel cpt_unpairB1 (cpt_const [])
    (cpt_sel hrest (cpt_const []) (cpt_sel hall (cpt_const []) (cpt_sel hv' (cpt_const []) hout)))
  refine bf_cptl h (fun s => ?_)
  let inner := (unpairB (unpairB s).2).2
  let prior := (unpairB inner).1
  let witness := (unpairB (unpairB inner).2).1
  have he : sel prior [true] (bflag (prior.tail.lex witness ltBit)) = bflag (allowed prior witness) := by
    cases prior <;> cases eb : prior.tail.lex witness ltBit <;> simp [allowed,sel,bflag,eb]
  let rem := (unpairB inner).2
  let input := (unpairB (unpairB s).2).1
  let verify := sel (bflag (v (input,witness))) [] (certificateState input (true::witness) (unpairB rem).2)
  change sel (unpairB s).1 [] (sel rem [] (sel
    (sel prior [true] (bflag (prior.tail.lex witness ltBit))) [] verify)) =
    sel (unpairB s).1 [] (sel rem [] (sel (bflag (allowed prior witness)) [] verify))
  rw [he]

private theorem certificateStep_size (v : Verifier) (s : Word) :
    (certificateStep v s).length ≤ s.length + 7 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have h₃ := unpairB_length (unpairB (unpairB s).2).2
  have h₄ := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  unfold certificateStep
  dsimp only
  unfold sel
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · simp only [certificateState,pairB_length,List.length_cons,List.length_nil]
          omega

private def certificateDone (s : Word) : Bool :=
  !(unpairB s).1.isEmpty && (unpairB (unpairB (unpairB s).2).2).2.isEmpty

private theorem certificateDone_cpt :
    ComputableInPolyTime (fun x : Word => x) Computability.encodeBool certificateDone := by
  have hrest := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have h := cpt_comp (cpt_sel cpt_unpairB1 (cpt_const [])
    (cpt_sel hrest (cpt_const [true]) (cpt_const []))) bf_cpt_neL
  refine bf_cptl h (fun s => ?_)
  unfold certificateDone
  cases (unpairB s).1 <;> cases (unpairB (unpairB (unpairB s).2).2).2 <;> rfl

private def verifierRun (v : Verifier) (q : Word × Word) : Bool :=
  let (x,fuel) := unpairB q.1
  certificateDone ((certificateStep v)^[fuel.length] (certificateState x [] q.2))

private theorem verifierRun_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (verifierRun v) := by
  have hx := cpt_unpairB1_1 cpt_unpairB1
  have hfuel := cpt_unpairB2_1 cpt_unpairB1
  have hinit := cpt_pairB2 (cpt_const [true])
    (cpt_pairB2 hx (cpt_pairB2 (cpt_const []) cpt_unpairB2))
  have hi := cpt_iterGrow (certificateStep_cpt hv) 7 (certificateStep_size v) hfuel hinit
  have h := cpt_comp hi certificateDone_cpt
  exact cpt_fromRawBool (f := verifierRun v) h

private theorem certificateStep_spec (v : Verifier) (x prior rest : Word) :
    certificateStep v (certificateState x prior rest) =
      if rest ≠ [] ∧ allowed prior (unpairB rest).1 = true ∧ v (x,(unpairB rest).1) = true
      then certificateState x (true :: (unpairB rest).1) (unpairB rest).2 else [] := by
  cases rest with
  | nil => simp [certificateStep,certificateState,unpairB_pairB]
  | cons b bs =>
    cases ha : allowed prior (unpairB (b::bs)).1 <;>
      cases hv : v (x,(unpairB (b::bs)).1) <;>
      simp [certificateStep,certificateState,unpairB_pairB,sel,bflag,ha,hv]

private theorem deadCertificate (v : Verifier) (n : Nat) :
    (certificateStep v)^[n] [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl

private def follows (prior w : Word) : Prop := prior = [] ∨ prior.tail < w

private theorem follows_trans {prior w u : Word} (h : follows prior w) (hu : w < u) :
    follows prior u := by
  rcases h with e | lt
  · exact Or.inl e
  · exact Or.inr (lt.trans hu)

private theorem certificate_sound (v : Verifier) (x prior rest : Word) (n : Nat)
    (yes : certificateDone ((certificateStep v)^[n] (certificateState x prior rest)) = true) :
    ∃ xs : List Word, xs.length = n ∧ xs.Pairwise (· < ·) ∧
      ∀ w ∈ xs, v (x,w) = true ∧ follows prior w := by
  induction n generalizing prior rest with
  | zero => exact ⟨[],rfl,by simp,by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply,certificateStep_spec] at yes
    set w := (unpairB rest).1
    by_cases h : rest ≠ [] ∧ allowed prior w = true ∧ v (x,w) = true
    · rw [if_pos h] at yes
      obtain ⟨xs,hl,hs,hx⟩ := ih (true::w) (unpairB rest).2 yes
      have hf := (allowed_spec prior w).mp h.2.1
      have hlater (u : Word) (hu : u ∈ xs) : w < u := by
        simpa [follows] using (hx u hu).2
      refine ⟨w::xs,by simp [hl],List.pairwise_cons.mpr ⟨hlater,hs⟩,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hm
      · exact ⟨h.2.2,hf⟩
      · exact ⟨(hx u hm).1,follows_trans hf (hlater u hm)⟩
    · rw [if_neg h,deadCertificate] at yes
      contradiction

private theorem certificate_complete (v : Verifier) (x prior : Word) (xs : List Word)
    (sorted : xs.Pairwise (· < ·)) (admissible : ∀ w ∈ xs, v (x,w) = true ∧ follows prior w) :
    certificateDone ((certificateStep v)^[xs.length]
      (certificateState x prior (encodeFrontier xs))) = true := by
  induction xs generalizing prior with
  | nil => simp [certificateDone,certificateState,unpairB_pairB,encodeFrontier]
  | cons w ws ih =>
    have hw := admissible w (by simp)
    have hv := (allowed_spec prior w).mpr hw.2
    have he : encodeFrontier (w::ws) = pairB w (encodeFrontier ws) := rfl
    have hn := encodeFrontier_cons_ne w ws
    rw [he] at hn
    rw [List.length_cons,Function.iterate_succ_apply,he,certificateStep_spec]
    rw [unpairB_pairB, if_pos ⟨hn,hv,hw.1⟩]
    exact ih (true::w) sorted.of_cons (fun u hu =>
      ⟨(admissible u (List.mem_cons_of_mem _ hu)).1,
        Or.inr ((List.pairwise_cons.mp sorted).1 u hu)⟩)

/-- The unary distinct-witness threshold of any measured polynomially bounded
relation belongs to the pinned NP class, independently of sparse reductions. -/
theorem ThresholdWitnessNP (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ L : Language Bool, L ∈ NP ∧
      ∀ x fuel : Word,
        (List.replicate x.length true ++ false :: (x ++ fuel)) ∈ L ↔
          ∃ S : Finset Word, S.card = fuel.length ∧ ∀ w ∈ S, (x,w) ∈ R := by
  obtain ⟨v,hvSpec,hv⟩ := hR
  let L : Language Bool := {s | ∃ S : Finset Word, S.card = (unpairB s).2.length ∧
    ∀ w ∈ S, ((unpairB s).1,w) ∈ R}
  let V : Set (Word × Word) := {q | verifierRun v q = true}
  let cap : Polynomial Nat := (Polynomial.C 2 * p + 1) * Polynomial.X
  refine ⟨L,⟨V,cap,⟨verifierRun v,fun _ => Iff.rfl,verifierRun_cpt hv⟩,fun s => ?_⟩,
    fun x fuel => ?_⟩
  · let x := (unpairB s).1
    let fuel := (unpairB s).2
    change (∃ S : Finset Word, S.card = fuel.length ∧ ∀ w ∈ S, (x,w) ∈ R) ↔
      ∃ cert : Word, cert.length ≤ cap.eval s.length ∧ verifierRun v (s,cert) = true
    constructor
    · rintro ⟨S,hsize,hs⟩
      let xs := S.sort (· ≤ ·)
      have hsort := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S)
      have hlen : xs.length = fuel.length := (Finset.length_sort _).trans hsize
      have hl (w : Word) (hw : w ∈ xs) : (x,w) ∈ R := hs w (by simpa [xs] using hw)
      have hc := certificate_complete v x [] xs hsort
        (fun w hw => ⟨(hvSpec _).mp (hl w hw),Or.inl rfl⟩)
      refine ⟨encodeFrontier xs,?_,?_⟩
      · have h₀ := unpairB_length s
        have hx : x.length ≤ s.length := by dsimp [x]; omega
        have hy : fuel.length ≤ s.length := by dsimp [fuel]; omega
        have ha (w : Word) (hw : w ∈ xs) :=
          (bound x w (hl w hw)).trans (eval_mono p hx)
        have hb := (frontierSize (p.eval s.length) xs ha).trans
          (Nat.mul_le_mul_left _ (hlen.trans_le hy))
        simpa [cap] using hb
      · rw [hlen] at hc
        exact hc
    · rintro ⟨cert,_,hc⟩
      obtain ⟨xs,hsize,hs,hx⟩ := certificate_sound v x [] cert fuel.length hc
      have hn : xs.Nodup := hs.imp (fun h => ne_of_lt h)
      exact ⟨xs.toFinset,(List.toFinset_card_of_nodup hn).trans hsize,
        fun w hw => (hvSpec _).mpr ((hx w (List.mem_toFinset.mp hw)).1)⟩
  · change (∃ S : Finset Word, S.card = (unpairB (pairB x fuel)).2.length ∧
      ∀ w ∈ S, ((unpairB (pairB x fuel)).1,w) ∈ R) ↔ _
    rw [unpairB_pairB]

end PEqualNP.Outside
