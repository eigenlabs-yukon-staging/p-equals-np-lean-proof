import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private abbrev Raw := List Bool

private def tail (parse : Raw → Raw × Raw) (x : Raw) : Raw := (parse x).2

private def failure (parse : Raw → Raw × Raw) (query : Raw → Bool)
    (root rem : Raw) : Raw :=
  if rem = [] then [] else if query (pairB root (pairB (parse rem).2 (parse rem).1)) then [] else [true]

private theorem failure_cpt {parse : Raw → Raw × Raw} {query : Raw → Bool}
    (hp : ComputableInPolyTime (fun x : Raw => x) encodePair parse)
    (hv : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool query)
    {root rem : Raw → Raw}
    (hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) root)
    (hm : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) rem) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun x => failure parse query (root x) (rem x)) := by
  have hs := cpt_comp hm hp
  have ht := cpt_comp hs cpt_snd
  have hc := cpt_comp hs cpt_fst
  have hq := cpt_comp (cpt_pairB2 hr (cpt_pairB2 ht hc)) hv
  refine cptE (cpt_sel hm (cpt_const []) (cpt_sel (cpt_bitFlag hq) (cpt_const [true]) (cpt_const []))) (fun x => ?_)
  unfold failure
  by_cases h : rem x = []
  · simp [sel,h]
  · cases hq : query (pairB (root x) (pairB (parse (rem x)).2 (parse (rem x)).1)) <;> simp [sel,h,hq]

private theorem formula_cons (c : Clause) (φ : CNF) : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
  simp [encodeCNF]

private theorem formula_count (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [formula_cons,List.length_append,List.length_cons]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

def suffixChecks (valid : CNF → CNF → Clause → Prop) (root trace : CNF) : Prop :=
  ∀ (newer : CNF) (c : Clause) (older : CNF),
    trace = newer ++ c :: older → valid root older c

theorem suffixChecks_cons (valid : CNF → CNF → Clause → Prop) (φ ρ : CNF) (c : Clause) :
    suffixChecks valid φ (c :: ρ) ↔ valid φ ρ c ∧ suffixChecks valid φ ρ := by
  constructor
  · intro h
    exact ⟨h [] c ρ rfl,fun pre d suf he => h (c :: pre) d suf (congrArg (List.cons c) he)⟩
  · rintro ⟨hfirst,hrest⟩ pre d suf he
    cases pre with
    | nil =>
        change c :: ρ = d :: suf at he
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        exact hfirst
    | cons a pre =>
        have h := (List.cons.inj he).2
        exact hrest pre d suf h

private theorem failures_correct (parse : Raw → Raw × Raw) (query : Raw → Bool) (valid : CNF → CNF → Clause → Prop)
    (hp : ∀ (c : Clause) r, parse (encodeClause c ++ r) = (encodeClause c,r))
    (h0 : tail parse [] = [])
    (hv : ∀ (φ ρ : CNF) (c : Clause), query (pairB (encodeCNF φ) (pairB (encodeCNF ρ) (encodeClause c))) = true ↔ valid φ ρ c)
    (φ ρ : CNF) (n : ℕ) (hn : ρ.length ≤ n) :
    ((List.range n).flatMap (fun i => failure parse query (encodeCNF φ) ((tail parse)^[i] (encodeCNF ρ)))) = [] ↔
    suffixChecks valid φ ρ := by
  induction ρ generalizing n with
  | nil =>
      have h (i : ℕ) : (tail parse)^[i] ([] : Raw) = [] := by
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply,h0,ih]
      change ((List.range n).flatMap (fun i => failure parse query (encodeCNF φ) ((tail parse)^[i] []))) = [] ↔
        suffixChecks valid φ []
      simp only [h,failure,ite_true,List.flatMap_eq_nil_iff,implies_true,true_iff]
      intro pre c suf h
      cases pre <;> simp at h
  | cons c ρ ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hlen : ρ.length ≤ n := by simpa using hn
          have hnext (i : ℕ) :
              (tail parse)^[i+1] (encodeCNF (c :: ρ)) = (tail parse)^[i] (encodeCNF ρ) := by
            rw [Function.iterate_succ_apply,formula_cons,tail,hp]
          have htag : encodeCNF (c :: ρ) ≠ [] := by rw [formula_cons]; simp [encodeClause]
          have hc : failure parse query (encodeCNF φ) (encodeCNF (c :: ρ)) = [] ↔ valid φ ρ c := by
            dsimp only [failure]
            rw [ite_eq_right htag,formula_cons,hp]
            change (if query (pairB (encodeCNF φ) (pairB (encodeCNF ρ) (encodeClause c))) then [] else [true]) = [] ↔ _
            rw [← hv]
            cases query (pairB (encodeCNF φ) (pairB (encodeCNF ρ) (encodeClause c))) <;> decide
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,List.append_eq_nil_iff,suffixChecks_cons]
          simp only [hnext,Function.iterate_zero_apply]
          exact and_congr hc (ih n hlen)

/-- Lift a measured local clause test to all lines of a newest-first
canonical trace, passing the original formula and older suffix as inputs. -/
theorem MeasuredClauseSuffixChecks (valid : CNF → CNF → Clause → Prop)
    (query : List Bool → Bool)
    (hq : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool query)
    (hv : let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
      ∀ (φ ρ : CNF) (c : Clause),
        query (pair (encodeCNF φ) (pair (encodeCNF ρ) (encodeClause c))) = true ↔ valid φ ρ c) :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ ρ : CNF), test (encodeCNF φ,encodeCNF ρ) = true ↔
        ∀ (pre : CNF) (c : Clause) (older : CNF), ρ = pre ++ c :: older → valid φ older c := by
  obtain ⟨parse,hp,hjoin,hsem⟩ := measuredFirstClause_reassembles
  have ht : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (tail parse) :=
    cpt_comp (g := fun p : Raw × Raw => p.2) hp cpt_snd
  have hlen (s : Raw) : (tail parse s).length ≤ s.length := by
    have h := congrArg List.length (hjoin s)
    simp only [List.length_append] at h
    unfold tail
    omega
  let rem := fun s => (tail parse)^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hm : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) rem :=
    cpt_iterLen ht hlen cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let bad := fun s => failure parse query (unpairB (unpairB s).2).1 (rem s)
  have hb : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) bad :=
    failure_cpt hp hq (cpt_unpairB1_1 cpt_unpairB2) hm
  let collect := fun s => (List.range (unpairB s).2.length).flatMap (fun i => bad (pairB (un i) s))
  have hc : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) collect :=
    cpt_flatMapRange hb cpt_unpairB2 cpt_id
  let output := fun s => (collect s).isEmpty
  have ho := cpt_comp (g := fun w : Raw => !w.isEmpty)
    (cpt_sel hc (cpt_const [true]) (cpt_const [])) bf_cpt_neL
  have he : (fun s => !(sel (collect s) [true] []).isEmpty) = output := by
    funext s
    unfold output
    cases collect s <;> rfl
  rw [he] at ho
  refine ⟨fun p => output (pairB p.1 p.2),cpt_comp (g := output) cpt_pairB ho,fun φ ρ => ?_⟩
  simp only [output,collect,bad,rem,unpairB_pairB,un_length,List.isEmpty_iff]
  have h0 : tail parse [] = [] := (List.append_eq_nil_iff.mp (hjoin [])).2
  exact failures_correct parse query valid hsem h0 hv φ ρ _ (formula_count ρ)

end PEqualNP.Outside
