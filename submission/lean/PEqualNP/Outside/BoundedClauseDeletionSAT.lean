import PEqualNP.Outside.ExactPackedProductBudgetSAT
import PEqualNP.Outside.MeasuredClauseExtraction
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Library.L016
import PEqualNP.Library.L046
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

private def pack (base extra : CNF) : List Bool := pairB (encodeCNF base) (encodeCNF extra)

private def picked (base : CNF) (i : ℕ) : CNF := (getElem? base i).toList

private def admissible (G : Language Bool) (base : CNF) (r : ℕ) : Prop :=
  ∃ kept : CNF, kept.Sublist base ∧ base.length ≤ kept.length + r ∧ encodeCNF kept ∈ G

private theorem encode_app (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF,List.flatMap_append]

private theorem encode_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]

private theorem clause_bits (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      have h : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [h,List.length_append,List.length_cons]
      have h' : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega

private theorem formula_bits (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [encode_cons,List.length_append,List.length_cons]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

private theorem clause_le_code (φ : CNF) (c : Clause) (hc : c ∈ φ) : c.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp at hc
  | cons d φ ih =>
      rw [encode_cons,List.length_append]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (clause_bits c).trans (Nat.le_add_right _ _)
      · exact (ih hc).trans (Nat.le_add_left _ _)

private theorem product_le_power (φ : CNF) (x : ℕ) (h : ∀ c ∈ φ, c.length ≤ x) :
    (φ.map List.length).prod ≤ x ^ φ.length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      rw [Nat.mul_comm (x ^ φ.length) x]
      exact Nat.mul_le_mul (h c List.mem_cons_self) (ih fun d hd => h d (List.mem_cons_of_mem _ hd))

private theorem base_budget (base extra : CNF) (K : ℕ) (hk : extra.length ≤ K) :
    (extra.map List.length).prod ≤ ((Polynomial.X + 1 : Polynomial ℕ)^K).eval (pack base extra).length := by
  let n := (pack base extra).length
  have hle : (encodeCNF extra).length ≤ n := by
    dsimp only [n,pack]
    rw [pairB_length]
    omega
  have hprod := product_le_power extra (n+1) (fun c hc => (clause_le_code extra c hc).trans (by omega))
  have hmono := Nat.pow_le_pow_right (by omega : 0 < n+1) hk
  have he : ((Polynomial.X + 1 : Polynomial ℕ)^K).eval n = (n+1)^K := by simp
  exact (hprod.trans hmono).trans_eq he.symm

private theorem erase_site {kept base : CNF} (h : kept.Sublist base) (hlt : kept.length < base.length) :
    ∃ i < base.length, kept.Sublist (base.eraseIdx i) := by
  induction h with
  | slnil => simp at hlt
  | cons a h =>
      exact ⟨0,by simp,by simpa using h⟩
  | cons_cons a h ih =>
      obtain ⟨i,hi,hs⟩ := ih (by simpa using hlt)
      refine ⟨i+1,by simpa using hi,?_⟩
      exact List.Sublist.cons_cons a hs

private theorem picked_len (base : CNF) (i : ℕ) :
    (base.eraseIdx i).length + (picked base i).length = base.length := by
  by_cases hi : i < base.length
  · simp only [picked,List.getElem?_eq_getElem hi,Option.toList_some,List.length_cons,List.length_nil,
      List.length_eraseIdx_of_lt hi]
    omega
  · have hle : base.length ≤ i := by omega
    simp [picked,List.getElem?_eq_none hle,List.eraseIdx_of_length_le hle]

private theorem picked_members (base : CNF) (i : ℕ) (c : Clause) :
    c ∈ base ↔ c ∈ base.eraseIdx i ∨ c ∈ picked base i := by
  by_cases hi : i < base.length
  · have e : base.take i ++ base[i] :: base.drop (i+1) = base := by
      rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
    have h : c ∈ base.take i ++ base[i] :: base.drop (i+1) ↔ c ∈ base := by rw [e]
    rw [← h,List.eraseIdx_eq_take_drop_succ]
    simp only [picked,List.getElem?_eq_getElem hi,Option.toList_some,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have hle : base.length ≤ i := by omega
    simp [picked,List.getElem?_eq_none hle,List.eraseIdx_of_length_le hle]

private theorem move_sat (base extra : CNF) (i : ℕ) :
    Satisfiable (base.eraseIdx i ++ (extra ++ picked base i)) ↔ Satisfiable (base ++ extra) := by
  apply exists_congr
  intro σ
  simp only [CNF.eval,List.all_eq_true,List.mem_append]
  constructor
  · intro h c hc
    rcases hc with hc | hc
    · rcases (picked_members base i c).mp hc with hc | hc
      · exact h c (Or.inl hc)
      · exact h c (Or.inr (Or.inr hc))
    · exact h c (Or.inr (Or.inl hc))
  · intro h c hc
    rcases hc with hc | hc | hc
    · exact h c (Or.inl ((picked_members base i c).mpr (Or.inl hc)))
    · exact h c (Or.inr hc)
    · exact h c (Or.inl ((picked_members base i c).mpr (Or.inr hc)))

private theorem admissible_zero (G : Language Bool) (base : CNF) :
    admissible G base 0 ↔ encodeCNF base ∈ G := by
  constructor
  · rintro ⟨kept,hsub,hlen,hG⟩
    have h := hsub.eq_of_length_le (by simpa using hlen)
    rwa [h] at hG
  · intro h
    exact ⟨base,List.Sublist.refl _,by simp,h⟩

private theorem admissible_step (G : Language Bool) (base : CNF) (r : ℕ) :
    admissible G base (r+1) ↔ ∃ i ≤ base.length, admissible G (base.eraseIdx i) r := by
  constructor
  · rintro ⟨kept,hsub,hlen,hG⟩
    by_cases he : kept = base
    · subst kept
      refine ⟨base.length,le_rfl,?_⟩
      rw [List.eraseIdx_of_length_le le_rfl]
      exact ⟨base,hsub,by omega,hG⟩
    · have hlt : kept.length < base.length := by
        by_contra hn
        exact he (hsub.eq_of_length_le (by omega))
      obtain ⟨i,hi,hs⟩ := erase_site hsub hlt
      refine ⟨i,hi.le,kept,hs,?_,hG⟩
      rw [List.length_eraseIdx_of_lt hi]
      omega
  · rintro ⟨i,_,kept,hsub,hlen,hG⟩
    refine ⟨kept,hsub.trans (List.eraseIdx_sublist base i),?_,hG⟩
    have := List.le_length_eraseIdx base i
    omega

private theorem exact_packed_sem (G B : Language Bool)
    (hG : G ∈ P) (hB : B ∈ P)
    (hbase : ∀ base : CNF, encodeCNF base ∈ G → ∀ units : CNF, IsKCNF 1 units →
      (encodeCNF (base ++ units) ∈ B ↔ Satisfiable (base ++ units))) (K r : ℕ) :
    ∃ D : Language Bool, D ∈ P ∧ ∀ base extra : CNF, extra.length + r ≤ K →
      (pack base extra ∈ D ↔ admissible G base r ∧ Satisfiable (base ++ extra)) := by
  induction r with
  | zero =>
      let q : Polynomial ℕ := (Polynomial.X+1)^K
      let D : Language Bool := {x | ∃ (b e : CNF), pack b e = x ∧
        encodeCNF b ∈ G ∧ (e.map List.length).prod ≤ q.eval x.length ∧ Satisfiable (b ++ e)}
      have hD : D ∈ P := ExactPackedProductBudgetSAT G B hG hB hbase q
      refine ⟨D,hD,fun base extra hlen => ?_⟩
      rw [admissible_zero]
      constructor
      · rintro ⟨b,e,hp,hb,_,hs⟩
        have he := congrArg unpairB hp
        simp only [pack,unpairB_pairB,Prod.mk.injEq] at he
        obtain ⟨he1,he2⟩ := he
        have hb' := PEqualNP.Library.SearchHelpers.encodeCNF_injective he1
        have he' := PEqualNP.Library.SearchHelpers.encodeCNF_injective he2
        subst b
        subst e
        exact ⟨hb,hs⟩
      · rintro ⟨hb,hs⟩
        exact ⟨base,extra,rfl,hb,base_budget base extra K (by simpa using hlen),hs⟩
  | succ r ih =>
      obtain ⟨prev,hprev,hsem⟩ := ih
      obtain ⟨pull,hpull,hps⟩ := MeasuredClauseExtraction
      let R : Set (List Bool × List Bool) := {x | x.2 ∈ prev}
      have hR : DecidableInPolyTime encodePair R := by
        obtain ⟨f,hf,hc⟩ := hprev
        exact ⟨fun x => f x.2,fun x => hf x.2,cpt_comp cpt_snd hc⟩
      let clock := fun x => true :: (unpairB x).1
      let gen := fun z : List Bool × List Bool =>
        let moved := pull (z.1,(unpairB z.2).1)
        pairB moved.1 ((unpairB z.2).2 ++ moved.2)
      have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen := by
        have hbase' := cpt_comp cpt_snd cpt_unpairB1
        have hextra := cpt_comp cpt_snd cpt_unpairB2
        have hm := cpt_comp (cpt_pairG cpt_fst hbase') hpull
        exact cpt_comp (cpt_pairG (cpt_comp hm cpt_fst)
          (cpt_comp (cpt_pairG hextra (cpt_comp hm cpt_snd)) cpt_append)) cpt_pairB
      let D : Language Bool := {x | ∃ i < (clock x).length, (x,gen (List.replicate i true,x)) ∈ R}
      refine ⟨D,IndexedWitnessProjection R hR clock (cpt_cons1 true cpt_unpairB1) gen hg,
        fun base extra hlen => ?_⟩
      let x := pack base extra
      have hgen (i : ℕ) : gen (List.replicate i true,x) =
          pack (base.eraseIdx i) (extra ++ picked base i) := by
        simp only [gen,x,pack,unpairB_pairB,hps,List.length_replicate,picked,encode_app]
      have hb (i : ℕ) : (extra ++ picked base i).length + r ≤ K := by
        have hp : (picked base i).length ≤ 1 := by
          unfold picked
          cases getElem? base i <;> simp
        simp only [List.length_append]
        omega
      have hr (i : ℕ) : gen (List.replicate i true,x) ∈ prev ↔
          admissible G (base.eraseIdx i) r ∧ Satisfiable (base ++ extra) := by
        rw [hgen,hsem _ _ (hb i),move_sat]
      change (∃ i < (clock x).length, gen (List.replicate i true,x) ∈ prev) ↔ _
      constructor
      · rintro ⟨i,_,hi⟩
        obtain ⟨ha,hs⟩ := (hr i).mp hi
        have he : base.eraseIdx (min i base.length) = base.eraseIdx i := by
          by_cases hm : i ≤ base.length
          · rw [Nat.min_eq_left hm]
          · have hle : base.length ≤ i := by omega
            rw [Nat.min_eq_right hle,List.eraseIdx_of_length_le hle,List.eraseIdx_of_length_le le_rfl]
        exact ⟨(admissible_step G base r).mpr ⟨min i base.length,Nat.min_le_right _ _,he.symm ▸ ha⟩,hs⟩
      · rintro ⟨ha,hs⟩
        obtain ⟨i,hi,hrem⟩ := (admissible_step G base r).mp ha
        refine ⟨i,?_,(hr i).mpr ⟨hrem,hs⟩⟩
        simp only [clock,x,pack,unpairB_pairB,List.length_cons]
        have hsize := formula_bits base
        omega

private theorem canonical_in_p : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x} ∈ P := by
  have h := cpt_comp (g := fun l : List Bool => !l.isEmpty)
    PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF bf_cpt_neL
  have he : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
    funext s
    cases wfB s <;> rfl
  rw [he] at h
  exact ⟨wfB,fun s => (wfB_iff s).symm,h⟩

/-- Exact SAT with a fixed number of deletions to a measured tractable base family. -/
theorem BoundedClauseDeletionSAT (G B : Language Bool) (hG : G ∈ P) (hB : B ∈ P)
    (hbase : ∀ base : CNF, encodeCNF base ∈ G → ∀ units : CNF, IsKCNF 1 units →
      (encodeCNF (base ++ units) ∈ B ↔ Satisfiable (base ++ units))) (k : ℕ) :
    {x : List Bool | ∃ (φ kept : CNF), encodeCNF φ = x ∧ List.Sublist kept φ ∧
      φ.length ≤ kept.length + k ∧ encodeCNF kept ∈ G ∧ Satisfiable φ} ∈ P := by
  obtain ⟨D,hD,hspec⟩ := exact_packed_sem G B hG hB hbase k k
  let W : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  let A : Language Bool := {x | pairB x [] ∈ D}
  have hA := L016 A D ⟨fun x => pairB x [],cpt_pairB2 cpt_id (cpt_const []),fun _ => Iff.rfl⟩ hD
  have h := L046 W A canonical_in_p hA
  have he (φ : CNF) : encodeCNF φ ∈ A ↔ admissible G φ k ∧ Satisfiable φ := by
    change pack φ [] ∈ D ↔ _
    simpa only [List.append_nil] using hspec φ [] (by simp)
  have hset : {x : List Bool | ∃ (φ kept : CNF), encodeCNF φ = x ∧ List.Sublist kept φ ∧
      φ.length ≤ kept.length + k ∧ encodeCNF kept ∈ G ∧ Satisfiable φ} = W ⊓ A := by
    ext x
    change (∃ (φ kept : CNF), encodeCNF φ = x ∧ List.Sublist kept φ ∧
      φ.length ≤ kept.length + k ∧ encodeCNF kept ∈ G ∧ Satisfiable φ) ↔
      (∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ A
    constructor
    · rintro ⟨φ,kept,rfl,hs,hl,hG',hSat⟩
      exact ⟨⟨φ,rfl⟩,(he φ).mpr ⟨⟨kept,hs,hl,hG'⟩,hSat⟩⟩
    · rintro ⟨⟨φ,rfl⟩,ha⟩
      obtain ⟨⟨kept,hs,hl,hG'⟩,hSat⟩ := (he φ).mp ha
      exact ⟨φ,kept,rfl,hs,hl,hG',hSat⟩
  rwa [hset]

end PEqualNP.Outside
