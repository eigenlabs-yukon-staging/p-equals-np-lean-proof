import PEqualNP.Outside.VariableDeletionCorrect
import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

private abbrev Raw := List Bool
private abbrev Change := Raw × Raw → Raw

private def child (erase assign : Change) (s l : Raw) : Raw :=
  pairB (erase (l.tail.tail,(unpairB s).1)) (assign (l.tail.tail,(unpairB s).2))

private theorem child_cpt {erase assign : Change}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (ha : ComputableInPolyTime encodePair (fun x : Raw => x) assign) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (fun p => child erase assign p.1 p.2) := by
  let key := fun u : Raw => (unpairB u).2.tail.tail
  have hk : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) key :=
    cpt_tail1 (cpt_tail1 cpt_unpairB2)
  have hshape := cpt_comp (cpt_pair hk (cpt_unpairB1_1 cpt_unpairB1)) he
  have hval := cpt_comp (cpt_pair hk (cpt_unpairB2_1 cpt_unpairB1)) ha
  have hc := cpt_comp cpt_pairB (cpt_pairB2 hshape hval)
  simpa [unpairB_pairB,key,child] using hc

private theorem both_cpt {erase pos neg : Change} {f : Raw → Raw}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg)
    (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f) :
    ComputableInPolyTime encodePair (fun x : Raw => x)
      (fun p => f (child erase pos p.1 p.2) ++ f (child erase neg p.1 p.2)) :=
  cpt_comp (cpt_pairG (cpt_comp (child_cpt he hp) hf) (cpt_comp (child_cpt he hn) hf)) cpt_append

private theorem scan_cpt (f : Raw → Raw) (erase pos neg : Change)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg)
    (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f) :
    ∃ scan : Raw → Raw,
      ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) scan ∧
      ∀ φ : CNF, ∀ ψ : CNF,
        let s := pairB (encodeCNF φ) (encodeCNF ψ)
        scan s = φ.flatMap (fun c => c.flatMap (fun l =>
          f (child erase pos s (encodeLiteral l)) ++ f (child erase neg s (encodeLiteral l)))) := by
  obtain ⟨scanL,hl,hls⟩ := MeasuredLiteralMap _ (both_cpt he hp hn hf)
  obtain ⟨scanC,hc,hcs⟩ := MeasuredClauseMap scanL hl
  let scan := fun s => scanC (s,(unpairB s).1)
  refine ⟨scan,cpt_comp (cpt_pair cpt_id cpt_unpairB1) hc,fun φ ψ => ?_⟩
  simp only [scan,unpairB_pairB,hcs,hls]

private theorem raw_solver (G D : Language Bool) (hG : G ∈ P) (hD : D ∈ P)
    (hsub : ∀ φ ψ : CNF, ψ.Sublist φ → encodeCNF φ ∈ G → encodeCNF ψ ∈ G)
    (hDspec : ∀ φ : CNF, encodeCNF φ ∈ G → (encodeCNF φ ∈ D ↔ Satisfiable φ))
    (k : ℕ) :
    ∃ test : Raw → Raw,
      ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) test ∧
      ∀ φ ψ : CNF, ψ.Sublist φ →
        (test (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔
        hasDeletionSet (fun c => encodeCNF c ∈ G) k φ ∧ Satisfiable ψ) := by
  classical
  obtain ⟨g,hg,hcg⟩ := hG
  obtain ⟨d,hd,hcd⟩ := hD
  obtain ⟨erase,he,hes⟩ := MeasuredVariableRestriction none
  obtain ⟨pos,hp,hps⟩ := MeasuredVariableRestriction (some true)
  obtain ⟨neg,hn,hns⟩ := MeasuredVariableRestriction (some false)
  let base := fun s => sel (if g (unpairB s).1 then [true] else []) [] (if d (unpairB s).2 then [true] else [])
  have hbase : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) base :=
    cpt_sel (cpt_bitFlag (cpt_comp cpt_unpairB1 hcg)) (cpt_const [])
      (cpt_bitFlag (cpt_comp cpt_unpairB2 hcd))
  have hbs (φ ψ : CNF) (hs : ψ.Sublist φ) :
      base (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔
      encodeCNF φ ∈ G ∧ Satisfiable ψ := by
    have h : base (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔
        g (encodeCNF φ) = true ∧ d (encodeCNF ψ) = true := by
      simp only [base,unpairB_pairB]
      cases g (encodeCNF φ) <;> cases d (encodeCNF ψ) <;> decide
    rw [h,← hg,← hd]
    exact and_congr_right (fun h => hDspec ψ (hsub φ ψ hs h))
  have her (φ : CNF) (x : ℕ) : erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ) := by
    simpa [eraseVariable,vcode] using hes x φ
  have hchild (φ ψ : CNF) (l : Literal) :
      (child erase pos (pairB (encodeCNF φ) (encodeCNF ψ)) (encodeLiteral l),
        child erase neg (pairB (encodeCNF φ) (encodeCNF ψ)) (encodeLiteral l)) =
      (pairB (encodeCNF (eraseVariable l.1 φ)) (encodeCNF (restrict l.1 true ψ)),
        pairB (encodeCNF (eraseVariable l.1 φ)) (encodeCNF (restrict l.1 false ψ))) := by
    have hpt (x : ℕ) (p : CNF) : pos (vcode x,encodeCNF p) = encodeCNF (restrict x true p) := hps x p
    have hnt (x : ℕ) (p : CNF) : neg (vcode x,encodeCNF p) = encodeCNF (restrict x false p) := hns x p
    simp only [child,encodeLiteral_eq,List.tail_cons,unpairB_pairB,her,hpt,hnt]
  induction k with
  | zero =>
      exact ⟨base,hbase,fun φ ψ hs => (hbs φ ψ hs).trans
        (and_congr_left (fun _ => (hasDeletionSet_zero (fun c => encodeCNF c ∈ G) φ).symm))⟩
  | succ k ih =>
      obtain ⟨test,ht,hts⟩ := ih
      obtain ⟨scan,hscan,hss⟩ := scan_cpt test erase pos neg he hp hn ht
      refine ⟨fun s => base s ++ scan s,cpt_app2 hbase hscan,fun φ ψ hs => ?_⟩
      let s := pairB (encodeCNF φ) (encodeCNF ψ)
      have hchild' (l : Literal) :
          (test (child erase pos s (encodeLiteral l)) ++ test (child erase neg s (encodeLiteral l))) ≠ [] ↔
          hasDeletionSet (fun c => encodeCNF c ∈ G) k (eraseVariable l.1 φ) ∧ Satisfiable ψ := by
        have hpos := congrArg Prod.fst (hchild φ ψ l)
        have hneg := congrArg Prod.snd (hchild φ ψ l)
        change child erase pos s (encodeLiteral l) =
          pairB (encodeCNF (eraseVariable l.1 φ)) (encodeCNF (restrict l.1 true ψ)) at hpos
        change child erase neg s (encodeLiteral l) =
          pairB (encodeCNF (eraseVariable l.1 φ)) (encodeCNF (restrict l.1 false ψ)) at hneg
        simp only [hpos,hneg,ne_eq,List.append_eq_nil_iff,not_and_or,
          hts _ _ (restrict_sublist_erase l.1 true hs), hts _ _ (restrict_sublist_erase l.1 false hs)]
        constructor
        · rintro (⟨ha,hd⟩ | ⟨ha,hd⟩)
          · exact ⟨ha,(satisfiable_split ψ l.1).mpr ⟨true,hd⟩⟩
          · exact ⟨ha,(satisfiable_split ψ l.1).mpr ⟨false,hd⟩⟩
        · rintro ⟨ha,hd⟩
          obtain ⟨b,h⟩ := (satisfiable_split ψ l.1).mp hd
          cases b
          · exact Or.inr ⟨ha,h⟩
          · exact Or.inl ⟨ha,h⟩
      have hscan' : scan s ≠ [] ↔ ∃ c ∈ φ, ∃ l ∈ c,
          hasDeletionSet (fun c => encodeCNF c ∈ G) k (eraseVariable l.1 φ) ∧ Satisfiable ψ := by
        change scan (pairB (encodeCNF φ) (encodeCNF ψ)) ≠ [] ↔ _
        rw [hss φ ψ]
        simp only [ne_eq,List.flatMap_eq_nil_iff,not_forall,exists_prop]
        exact exists_congr (fun c => and_congr_right (fun _ =>
          exists_congr (fun l => and_congr_right (fun _ => hchild' l))))
      change base s ++ scan s ≠ [] ↔ _
      have hb : base s ≠ [] ↔ encodeCNF φ ∈ G ∧ Satisfiable ψ := hbs φ ψ hs
      rw [show (base s ++ scan s ≠ []) ↔ (base s ≠ [] ∨ scan s ≠ []) by
        simp only [ne_eq,List.append_eq_nil_iff,not_and_or],hb,hscan',hasDeletionSet_step]
      constructor
      · rintro (⟨hg,hSat⟩ | ⟨c,hc,l,hl,ha,hSat⟩)
        · exact ⟨Or.inl hg,hSat⟩
        · exact ⟨Or.inr ⟨c,hc,l,hl,ha⟩,hSat⟩
      · rintro ⟨hg | ⟨c,hc,l,hl,ha⟩,hSat⟩
        · exact Or.inl ⟨hg,hSat⟩
        · exact Or.inr ⟨c,hc,l,hl,ha,hSat⟩

/-- For any sublist-closed guarded tractable base, fixed-size occurrence
deletion backdoors can be recognized while deciding a residual CNF. -/
theorem MeasuredVariableDeletionSAT (G D : Language Bool) (hG : G ∈ P) (hD : D ∈ P)
    (hsub : ∀ φ ψ : CNF, ψ.Sublist φ → encodeCNF φ ∈ G → encodeCNF ψ ∈ G)
    (hDspec : ∀ φ : CNF, encodeCNF φ ∈ G → (encodeCNF φ ∈ D ↔ Satisfiable φ)) (k : ℕ) :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ φ ψ : CNF, ψ.Sublist φ → (test (encodeCNF φ,encodeCNF ψ) = true ↔
        (∃ xs : List ℕ, xs.length ≤ k ∧
          encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G) ∧ Satisfiable ψ) := by
  obtain ⟨run,hr,h⟩ := raw_solver G D hG hD hsub hDspec k
  refine ⟨fun p => !(run (pairB p.1 p.2)).isEmpty,
    cpt_comp (g := fun w : Raw => !w.isEmpty) (cpt_comp cpt_pairB hr) bf_cpt_neL,fun φ ψ hs => ?_⟩
  simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff]
  exact h φ ψ hs

end PEqualNP.Outside
