import PEqualNP.Outside.OptimalWitnessCheckingInCoNP
import PEqualNP.Library.L031
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Outside.SatCodePrimitives

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

private abbrev Word := List Bool
private abbrev WRel := Set (Word × Word)

private def dummy (x : Word) : Word := un (x.length + 2)

private theorem dummy_cpt : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) dummy := by
  have h := L055 (Polynomial.X + 2)
  exact PEqualNP.Outside.SatCodePrimitives.cptl h (fun x => by simp [dummy, un])

private theorem dummy_length (x : Word) : (dummy x).length = x.length + 2 := by
  simp [dummy, un_length]

private def feasible : WRel :=
  {q | q.2 = dummy q.1 ∨ q.2.head? = some false ∧ SV (q.1, q.2.tail) = true}

private theorem feasible_cpt : DecidableInPolyTime encodePair feasible := by
  let f (z : Word) := (unpairB z).2
  let check (z : Word) :=
    (sel (bflag (decide (f z = dummy (unpairB z).1)))
      (sel (f z) [true] (sel (bflag ((f z).headD false))
        (sel (bflag (SV ((unpairB z).1, (f z).tail))) [true] []) [true]))
      []).isEmpty
  let dec (q : Word × Word) := check (pairB q.1 q.2)
  have hF : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) f := cpt_unpairB2
  have hEq := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hF (cpt_comp cpt_unpairB1 dummy_cpt)
  have hfirst := cpt_comp hF PEqualNP.Outside.SatCodePrimitives.cpt_firstF
  have hSat := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 (cpt_tail1 hF)) cpt_SV)
  have ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool check := by
    have h := cpt_comp (cpt_sel hEq (cpt_sel hF (cpt_const [true])
      (cpt_sel hfirst (cpt_sel hSat (cpt_const [true]) (cpt_const [])) (cpt_const [true])))
      (cpt_const [])) cpt_isEmpty
    exact h
  refine ⟨dec, ?_, cpt_comp cpt_pairB ht⟩
  rintro ⟨x, w⟩
  by_cases h : w = dummy x
  · simp [feasible, dec, check, f, unpairB_pairB, h, bflag, sel]
  · cases w with
    | nil => simp [feasible, dec, check, f, unpairB_pairB, h, bflag, sel]
    | cons b v => cases hSV : SV (x, v) <;> cases b <;>
      simp [feasible, dec, check, f, unpairB_pairB, h, bflag, sel, hSV]

private def shorterRel : WRel := {q | (unpairB q.2).1.length < (unpairB q.2).2.length}

private theorem cmp_cpt : DecidableInPolyTime encodePair shorterRel := by
  let decideLen (q : Word × Word) :=
    decide ((unpairB q.2).2.length ≤ (unpairB q.2).1.length)
  have ht : ComputableInPolyTime encodePair Computability.encodeBool decideLen := by
    have h := cpt_comp (cpt_comp cpt_snd cpt_unpairB) LenCmp.lenLE_polyTime
    exact h
  have hc := cpt_comp (cpt_bitFlag ht) cpt_isEmpty
  let dec (q : Word × Word) := (bflag (decideLen q)).isEmpty
  refine ⟨dec, ?_, hc⟩
  intro q
  by_cases he : (unpairB q.2).2.length ≤ (unpairB q.2).1.length
  · simp [shorterRel, dec, decideLen, bflag, he, Nat.not_lt.mpr he]
  · simp [shorterRel, dec, decideLen, bflag, he, Nat.lt_of_not_ge he]

theorem PEqualNP.Outside.ShortestWitnessCheckingCoNPComplete :
    ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ) (L : Language Bool),
      DecidableInPolyTime encodePair R ∧ L ∈ coNP ∧
      (∀ A ∈ coNP, PolyTimeReducible A L) ∧
      ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R → w.length ≤ v.length := by
  let p : Polynomial ℕ := Polynomial.X + 2
  obtain ⟨L, hL, hs⟩ :=
    PEqualNP.Outside.OptimalWitnessCheckingInCoNP feasible shorterRel p feasible_cpt cmp_cpt
  have hspec (x w : Word) : pairB x w ∈ L ↔
      w.length ≤ p.eval x.length ∧ (x, w) ∈ feasible ∧
      ∀ v : Word, v.length ≤ p.eval x.length → (x, v) ∈ feasible → w.length ≤ v.length := by
    refine (hs x w).trans ?_
    have h (v : Word) : (x, pairB v w) ∉ shorterRel ↔ w.length ≤ v.length := by
      simp [shorterRel, unpairB_pairB]
    exact and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun v => imp_congr_right fun _ => imp_congr_right fun _ => h v
  refine ⟨feasible, p, L, feasible_cpt, hL, ?_, hspec⟩
  have hreduce (x : Word) : pairB x (dummy x) ∈ L ↔ x ∉ SAT := by
    rw [hspec]
    refine ⟨?_, ?_⟩
    · intro h hs
      obtain ⟨w, hw, hv⟩ := (SV_spec x).mp hs
      have hl : (false :: w : Word).length ≤ p.eval x.length := by simp [p]; omega
      have hf : (x, false :: w) ∈ feasible := Or.inr ⟨rfl, hv⟩
      have hh := h.2.2 (false :: w) hl hf
      simp only [List.length_cons, dummy_length] at hh
      omega
    · intro h
      refine ⟨by simp [dummy_length, p], Or.inl rfl, ?_⟩
      intro v hv hf
      rcases hf with he | ⟨ht, hsat⟩
      · change v = dummy x at he
        rw [he]
      · have hs : x ∈ SAT := by
          obtain ⟨φ, hφ, hmodel⟩ := (SV_iff _ _).mp hsat
          exact ⟨φ, hφ, asg v.tail, hmodel⟩
        exact False.elim (h hs)
  intro A hA
  obtain ⟨f, hf, hf'⟩ := L031.2 Aᶜ hA
  refine ⟨fun x => pairB (f x) (dummy (f x)), cpt_pairB2 hf (cpt_comp hf dummy_cpt), ?_⟩
  intro x
  have h := not_congr (hf' x)
  change (¬ x ∉ A) ↔ f x ∉ SAT at h
  exact (by simpa only [Classical.not_not] using h : x ∈ A ↔ f x ∉ SAT).trans (hreduce (f x)).symm
