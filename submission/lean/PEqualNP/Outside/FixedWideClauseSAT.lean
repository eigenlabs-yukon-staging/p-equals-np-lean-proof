import PEqualNP.Library.L030
import PEqualNP.Library.L016
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Outside.MeasuredLiteralChoice
import PEqualNP.Outside.IndexedWitnessProjection

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private def rawQuery (base extra : CNF) : List Bool :=
  pairB (encodeCNF base) (encodeCNF extra)

private theorem kcnf_add_unit (base : CNF) (hbase : IsKCNF 2 base) (l : Option Literal) :
    IsKCNF 2 (base ++ [l.toList]) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hbase c hc
  · have e := List.mem_singleton.mp hc
    subst c
    cases l <;> simp

private theorem eval_append (σ : Assignment) (base extra : CNF) :
    (base ++ extra).eval σ = true ↔ base.eval σ = true ∧ extra.eval σ = true := by
  simp [CNF.eval, List.all_append]

private theorem eval_cons (σ : Assignment) (c : Clause) (extra : CNF) :
    CNF.eval σ (c :: extra) = true ↔ c.eval σ = true ∧ extra.eval σ = true := by
  simp [CNF.eval]

private theorem unit_true (l : Option Literal) (σ : Assignment) :
    Clause.eval σ l.toList = true ↔ ∃ a, l = some a ∧ a.eval σ = true := by
  cases l <;> simp [Clause.eval]

private theorem clause_len_le (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      have h : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by
        simp only [encodeClause, List.flatMap_cons, List.append_assoc]
      rw [h, List.length_append, List.length_cons]
      have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega

/-- For any fixed number of extra clauses, arbitrary clause widths can be added to a
canonical 2-CNF base with a polynomial-time decision procedure on the packed encoding. -/
theorem FixedWideClauseSAT (k : ℕ) :
    ∃ D : Language Bool, D ∈ P ∧ ∀ (base extra : CNF),
      IsKCNF 2 base → extra.length ≤ k →
      (List.replicate (encodeCNF base).length true ++ false ::
        (encodeCNF base ++ encodeCNF extra) ∈ D ↔ Satisfiable (base ++ extra)) := by
  change ∃ D : Language Bool, D ∈ P ∧ ∀ (base extra : CNF),
    IsKCNF 2 base → extra.length ≤ k →
    (rawQuery base extra ∈ D ↔ Satisfiable (base ++ extra))
  induction k with
  | zero =>
      let D : Language Bool := {x | (unpairB x).1 ∈ KSAT 2}
      have hD := L016 D (KSAT 2) ⟨(fun x => (unpairB x).1), cpt_unpairB1, fun _ => Iff.rfl⟩ L030
      refine ⟨D, hD, fun base extra hbase hlen => ?_⟩
      have hnil : extra = [] := List.length_eq_zero_iff.mp (by omega)
      subst extra
      change (unpairB (pairB (encodeCNF base) (encodeCNF []))).1 ∈ KSAT 2 ↔ _
      rw [unpairB_pairB, List.append_nil]
      constructor
      · rintro ⟨φ, _, he, hs⟩
        exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective he) ▸ hs
      · intro hs
        exact ⟨base, hbase, rfl, hs⟩
  | succ k ih =>
      obtain ⟨prev, hp, hspec⟩ := ih
      obtain ⟨split, hs, _, hsplit⟩ := MeasuredFirstClause
      obtain ⟨pick, hpc, hpick⟩ := MeasuredLiteralChoice
      let R : Set (List Bool × List Bool) := {z | z.2 ∈ prev}
      have hR : DecidableInPolyTime encodePair R := by
        obtain ⟨f, hf, hc⟩ := hp
        exact ⟨fun z => f z.2, fun z => hf z.2, cpt_comp cpt_snd hc⟩
      let clock := fun x => true :: (unpairB x).2
      let gen := fun z : List Bool × List Bool =>
        let base := (unpairB z.2).1
        let rest := (unpairB z.2).2
        let (head, tail) := split rest
        if rest = [] then z.2 else pairB (base ++ pick (z.1,head)) tail
      have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen := by
        let input := fun s => (unpairB s).2
        have hinput : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) input :=
          cpt_unpairB2
        have hb := cpt_unpairB1_1 hinput
        have hr := cpt_unpairB2_1 hinput
        have hh := cpt_comp (cpt_comp hr hs) cpt_fst
        have ht := cpt_comp (cpt_comp hr hs) cpt_snd
        have hw := cpt_comp (cpt_pair cpt_unpairB1 hh) hpc
        have hraw := cpt_sel hr hinput (cpt_pairB2 (cpt_app2 hb hw) ht)
        have hraw' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
            (fun s => gen (unpairB s)) := by
          have he : (fun s => sel ((unpairB (unpairB s).2).2) ((unpairB s).2)
              (pairB ((unpairB (unpairB s).2).1 ++ pick ((unpairB s).1,
                (split (unpairB (unpairB s).2).2).1)) (split (unpairB (unpairB s).2).2).2)) =
              (fun s => gen (unpairB s)) := by
            funext s
            simp [gen, sel]
          rwa [← he]
        have hcomp := cpt_comp cpt_pairB hraw'
        have he : (fun p : List Bool × List Bool => gen (unpairB (pairB p.1 p.2))) = gen := by
          funext p
          simp only [unpairB_pairB]
        rwa [he] at hcomp
      let D : Language Bool := {x | ∃ i < (clock x).length,
        (x, gen (List.replicate i true, x)) ∈ R}
      refine ⟨D, IndexedWitnessProjection R hR clock (cpt_cons1 true cpt_unpairB2) gen hg,
        fun base extra hbase hlen => ?_⟩
      let x := rawQuery base extra
      change (∃ i < (clock x).length, gen (List.replicate i true, x) ∈ prev) ↔ _
      cases extra with
      | nil =>
          have hgen (i : ℕ) : gen (List.replicate i true, x) = rawQuery base [] := by
            simp [gen, x, rawQuery, unpairB_pairB, encodeCNF]
          have hs := hspec base [] hbase (by simp)
          constructor
          · rintro ⟨i, _, hi⟩
            exact hs.mp ((hgen i) ▸ hi)
          · intro hs'
            refine ⟨0, by simp [clock], ?_⟩
            exact (hgen 0).symm ▸ hs.mpr hs'
      | cons c extra =>
          have hl : extra.length ≤ k := by simpa using hlen
          have hrest : encodeCNF (c :: extra) = encodeClause c ++ encodeCNF extra := by
            simp [encodeCNF]
          have hne : encodeCNF (c :: extra) ≠ [] := by
            rw [hrest]
            simp [encodeClause]
          have hgen (i : ℕ) :
              gen (List.replicate i true, x) = rawQuery (base ++ [c[i]?.toList]) extra := by
            dsimp only [gen, x, rawQuery]
            simp only [unpairB_pairB, ite_eq_right hne]
            rw [hrest, hsplit, hpick, List.length_replicate]
            simp [encodeCNF]
          have hbranch (i : ℕ) :
              gen (List.replicate i true, x) ∈ prev ↔
                Satisfiable ((base ++ [c[i]?.toList]) ++ extra) := by
            rw [hgen, hspec _ _ (kcnf_add_unit base hbase _) hl]
          constructor
          · rintro ⟨i, _, hi⟩
            obtain ⟨σ, hσ⟩ := (hbranch i).mp hi
            obtain ⟨hb, he⟩ := (eval_append _ _ _).mp hσ
            obtain ⟨hb, hu⟩ := (eval_append _ _ _).mp hb
            have hu' : Clause.eval σ c[i]?.toList = true := by simpa [CNF.eval] using hu
            obtain ⟨a, ha, htrue⟩ := (unit_true _ σ).mp hu'
            have hmem : a ∈ c := List.mem_of_getElem? ha
            have hc : c.eval σ = true := List.any_eq_true.mpr ⟨a, hmem, htrue⟩
            exact ⟨σ, (eval_append _ _ _).mpr ⟨hb, (eval_cons _ _ _).mpr ⟨hc, he⟩⟩⟩
          · rintro ⟨σ, hσ⟩
            obtain ⟨hb, hrestTrue⟩ := (eval_append _ _ _).mp hσ
            obtain ⟨hc, he⟩ := (eval_cons _ _ _).mp hrestTrue
            obtain ⟨a, ha, hat⟩ := List.any_eq_true.mp hc
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
            have hil : i < c.length := by
              by_contra hn
              have hn' : c[i]? = none := List.getElem?_eq_none (by omega)
              rw [hn'] at hi
              simp at hi
            refine ⟨i, ?_, (hbranch i).mpr ⟨σ, ?_⟩⟩
            · simp only [clock, x, rawQuery, unpairB_pairB, List.length_cons, hrest, List.length_append]
              have hw := clause_len_le c
              omega
            · have hu : Clause.eval σ c[i]?.toList = true := (unit_true _ σ).mpr ⟨a, hi, hat⟩
              exact (eval_append _ _ _).mpr ⟨(eval_append _ _ _).mpr
                ⟨hb, by simpa [CNF.eval] using hu⟩, he⟩

end PEqualNP.Outside
