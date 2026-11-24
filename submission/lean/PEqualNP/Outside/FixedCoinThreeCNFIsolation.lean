import PEqualNP.Outside.FixedCoinTapeQueryIsolation
import PEqualNP.Outside.ParsimoniousCookLevin3
import PEqualNP.Outside.RecordMapMachine

namespace PEqualNP.Outside.FixedCoinThreeCNF
open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.OneHot (Models extend Mentioned)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordMapMachine (mapWord mapWord_cpt mapWord_enc)
open PEqualNP.Outside.FixedCoinTapeIsolation (tapeLength event Q tape_count batch_on_tape sound_query)
open PEqualNP.Outside.AffinePrefixBatchMachine (produce produce_cpt)
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt admissible source)
open PEqualNP.Outside.AffineIsolationQueryBatch (successful)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)
open PEqualNP.Library.Machines (cpt_comp eval_mono)

theorem accepts_bound (p : Polynomial ℕ) (dec : List Bool × List Bool → Bool)
    (z w : List Bool) (h : verify p dec (z,w) = true) :
    w.length ≤ p.eval z.length := by
  have hv : w.length ≤ p.eval (unpairB z).1.length := by
    simp [verify, admissible, source] at h
    exact of_decide_eq_true h.1.1
  have hl : (unpairB z).1.length ≤ z.length := by
    have hL := unpairB_length z
    omega
  exact hv.trans (eval_mono p hl)

theorem wire_fold (xs : List (List Bool)) :
    wire xs = xs.foldr (fun y rest => List.replicate y.length true ++ false :: (y ++ rest)) [] := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [wire,pairB,un,ih]

theorem sat_iff_models (φ : CNF) : Satisfiable φ ↔ Nonempty (Models φ) := by
  constructor
  · rintro ⟨σ,hσ⟩
    exact ⟨⟨fun i => σ i.1, (PEqualNP.Outside.OneHot.eval_restrict φ σ).trans hσ⟩⟩
  · rintro ⟨a⟩
    exact ⟨extend φ a.1,a.2⟩

theorem unique_model {α : Type} {φ : CNF} (e : α ≃ Models φ) (a : α)
    (h : ∀ b : α, b = a) :
    ∃! m : {i : ℕ // Mentioned φ i} → Bool, CNF.eval (extend φ m) φ = true := by
  have hu (m : Models φ) : m = e a := by
    rw [← e.apply_symm_apply m, h (e.symm m)]
  exact ⟨(e a).1,(e a).2,fun m hm => congrArg Subtype.val (hu ⟨m,hm⟩)⟩

end PEqualNP.Outside.FixedCoinThreeCNF

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Library.Universal (unpairB)
open PEqualNP.Outside.FixedCoinThreeCNF
open PEqualNP.Outside.FixedCoinTapeIsolation (tapeLength event Q tape_count batch_on_tape sound_query)
open PEqualNP.Outside.AffinePrefixBatchMachine (produce produce_cpt)
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt)
open PEqualNP.Outside.AffineIsolationQueryBatch (successful)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordMapMachine (mapWord mapWord_cpt mapWord_enc)
open PEqualNP.Library.Machines (cpt_comp)

theorem PEqualNP.Outside.FixedCoinThreeCNFIsolation :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (p : Polynomial ℕ)
        (B : (x : List Bool) →
          (Fin ((2 * p.eval x.length + 3) * (2 * p.eval x.length + 2)) → Bool) → List CNF)
        (generate : List Bool × List Bool → List Bool),
        ComputableInPolyTime encodePair (fun s : List Bool => s) generate ∧
        (∀ x u, generate (x, List.ofFn u) =
          ((B x u).map encodeCNF).foldr
            (fun y rest => List.replicate y.length true ++ false :: (y ++ rest)) []) ∧
        (∀ x u φ, φ ∈ B x u → IsKCNF 3 φ) ∧
        (∀ x ∉ L, ∀ u φ, φ ∈ B x u → ¬ Satisfiable φ) ∧
        ∀ x ∈ L,
          let n := (2 * p.eval x.length + 3) * (2 * p.eval x.length + 2)
          let U : CNF → Prop := fun φ =>
            ∃! a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool,
              CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                then a ⟨i,h⟩ else false) φ = true
          Fintype.card (Fin n → Bool) ≤ 8 *
            (@Finset.filter (Fin n → Bool) (fun u => ∃ φ ∈ B x u, U φ)
              (fun _ => Classical.propDecidable _) Finset.univ).card := by
  intro L hL
  obtain ⟨R,p,⟨dec,hd,hdec⟩,hL⟩ := hL
  let D := verify p dec
  obtain ⟨F,hF,hmodels⟩ := PEqualNP.Outside.ParsimoniousCookLevin3 D p (verify_cpt p dec hdec)
  let B (x : List Bool) (u : Fin (tapeLength (p.eval x.length)) → Bool) := (Q p x u).map F
  let G (x : List Bool × List Bool) := mapWord (fun z => encodeCNF (F z)) (produce p x)
  have hg : ComputableInPolyTime encodePair (fun s : List Bool => s) G :=
    cpt_comp (produce_cpt p) (mapWord_cpt _ hF)
  refine ⟨p,B,G,hg,?_,?_,?_,?_⟩
  · intro x u
    change mapWord (fun z => encodeCNF (F z)) (produce p (x,List.ofFn u)) = _
    calc
      _ = mapWord (fun z => encodeCNF (F z)) (wire (Q p x u)) :=
        congrArg (mapWord (fun z => encodeCNF (F z))) ((batch_on_tape p x u).trans (wire_fold _).symm)
      _ = _ := by
        rw [mapWord_enc,wire_fold]
        simp only [B,List.map_map,Function.comp_def]
  · intro x u φ hφ
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hφ
    exact (hmodels z).1
  · intro x hx u φ hφ hs
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hφ
    obtain ⟨e⟩ := (hmodels z).2
    obtain ⟨a⟩ := (sat_iff_models (F z)).mp hs
    have hw := sound_query R p dec hd x u z (e.symm a).1 hz (e.symm a).2.2
    exact hx ((hL x).mpr ⟨(e.symm a).1,(mem_goodWords R p x _).mp hw⟩)
  · intro x hx
    classical
    have hne : (goodWords R p x).Nonempty := by
      obtain ⟨w,hw⟩ := (hL x).mp hx
      exact ⟨w,(mem_goodWords R p x w).mpr hw⟩
    have hs := tape_count R p dec hd x hne
    refine hs.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card ?_))
    intro u hu
    have ⟨z,hz,w,hw,hpass,huniq⟩ := (Finset.mem_filter.mp hu).2
    have hz' : z ∈ Q p x u := List.mem_toFinset.mp hz
    obtain ⟨e⟩ := (hmodels z).2
    have hlen : w.length ≤ p.eval z.length := accepts_bound p dec z w hpass
    apply (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mpr
    refine ⟨Finset.mem_univ _,F z,List.mem_map.mpr ⟨z,hz',rfl⟩,?_⟩
    refine unique_model e ⟨w,hlen,hpass⟩ (fun other => ?_)
    apply Subtype.ext
    by_contra hne'
    have ho := sound_query R p dec hd x u z other.1 hz' other.2.2
    have he := huniq other.1 ho hne'
    have ha := other.2.2
    change verify p dec (z,other.1) = true at ha
    rw [he] at ha
    exact Bool.noConfusion ha
