import PEqualNP.Outside.ParsimoniousTableau
import PEqualNP.Outside.TableauWidth

namespace PEqualNP.Outside.CNFWidth
open PEqualNP.Search
open PEqualNP.Outside.OneHot (Mentioned mentioned_of_clause)

def liftLit (l : Literal) : Literal := (2*l.1, l.2)

def fresh (j : ℕ) : ℕ := 2*j+1

def splitClause (j : ℕ) (cl : Clause) : CNF :=
  match cl with
  | a :: b :: c :: d :: [] =>
    let A := liftLit a
    let B := liftLit b
    let C := liftLit c
    let D := liftLit d
    let r := fresh j
    [[A,B,(r,false)], [(A.1,!A.2),(r,true)], [(B.1,!B.2),(r,true)], [(r,true),C,D]]
  | cl => [cl.map liftLit]

def splitCNF (F : CNF) : CNF :=
  (List.range F.length).flatMap fun j => splitClause j (F[j]?.getD [])

theorem splitClause_ok (σ : Assignment) (j : ℕ) (cl : Clause) :
    CNF.eval σ (splitClause j cl) = true ↔
      Clause.eval (fun i => σ (2*i)) cl = true ∧
        (cl.length = 4 → σ (fresh j) =
          ((cl.take 2).any (Literal.eval (fun i => σ (2*i))))) := by
  have short (l : Clause) : Clause.eval σ (l.map liftLit) =
      Clause.eval (fun i => σ (2*i)) l := by
    simp only [Clause.eval,List.any_map]
    rfl
  match cl with
  | [] | [_] | [_,_] | [_,_,_] | _::_::_::_::_::_ =>
    simp only [splitClause,CNF.eval,List.all_cons,List.all_nil,Bool.and_true,short]
    simp
  | [a,b,c,d] =>
    have hn (l : Literal) : Literal.eval σ ((liftLit l).1, !(liftLit l).2) =
        !Literal.eval (fun i => σ (2*i)) l := by
      cases l with
      | mk i pol => cases pol <;> cases h : σ (2*i) <;> simp [Literal.eval,liftLit,h]
    have he (l : Literal) : Literal.eval σ (liftLit l) =
        Literal.eval (fun i => σ (2*i)) l := rfl
    simp only [splitClause,CNF.eval,Clause.eval,List.all_cons,List.all_nil,Bool.and_true,
      List.any_cons,List.any_nil,Bool.or_false,he,hn,List.length_cons,List.length_nil,
      List.take_succ_cons]
    simp only [show Literal.eval σ (fresh j,true) = σ (fresh j) by simp [Literal.eval],
      show Literal.eval σ (fresh j,false) = !σ (fresh j) by
        cases h : σ (fresh j) <;> simp [Literal.eval,h]]
    cases Literal.eval (fun i => σ (2*i)) a <;>
      cases Literal.eval (fun i => σ (2*i)) b <;>
      cases Literal.eval (fun i => σ (2*i)) c <;>
      cases Literal.eval (fun i => σ (2*i)) d <;>
      cases σ (fresh j) <;> simp


theorem index_cover (F : CNF) {cl : Clause} (hc : cl ∈ F) :
    ∃ j < F.length, F[j]?.getD [] = cl := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hc
  exact ⟨j,hj,by simpa [List.getElem?_eq_getElem hj] using he⟩

theorem splitCNF_ok (σ : Assignment) (F : CNF) :
    CNF.eval σ (splitCNF F) = true ↔
      CNF.eval (fun i => σ (2*i)) F = true ∧
        ∀ j < F.length, (F[j]?.getD []).length = 4 →
          σ (fresh j) = (((F[j]?.getD []).take 2).any
            (Literal.eval (fun i => σ (2*i)))) := by
  simp only [splitCNF,CNF.eval,List.all_eq_true,List.mem_flatMap]
  constructor
  · intro h
    have step (j : ℕ) (hj : j < F.length) :=
      (splitClause_ok σ j (F[j]?.getD [])).mp (List.all_eq_true.mpr fun cl hc =>
        h cl ⟨j, List.mem_range.mpr hj, hc⟩)
    refine ⟨?_, fun j hj => (step j hj).2⟩
    intro cl hc
    obtain ⟨j,hj,he⟩ := index_cover F hc
    exact he ▸ (step j hj).1
  · rintro ⟨h,ha⟩ cl ⟨j,hj,hc⟩
    have hj' := List.mem_range.mp hj
    have hm : F[j]?.getD [] ∈ F := by
      simpa [List.getElem?_eq_getElem hj'] using List.getElem_mem hj'
    have hb := (splitClause_ok σ j _).mpr ⟨h _ hm,ha j hj'⟩
    exact List.all_eq_true.mp hb cl hc

theorem splitClause_width (j : ℕ) (cl : Clause) (hc : cl.length ≤ 4) :
    IsKCNF 3 (splitClause j cl) := by
  match cl with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] =>
    simp [splitClause,IsKCNF]
  | _::_::_::_::_::_ =>
    simp only [List.length_cons] at hc
    omega

theorem split_width (F : CNF) (hF : IsKCNF 4 F) :
    IsKCNF 3 (splitCNF F) := by
  rw [splitCNF, PEqualNP.Outside.OneHot.width_flatMap]
  intro j hj
  have hj' := List.mem_range.mp hj
  apply splitClause_width
  simpa [List.getElem?_eq_getElem hj'] using hF F[j] (List.getElem_mem hj')


theorem mentioned_splitClause (j : ℕ) (cl : Clause) (x : ℕ) :
    Mentioned (splitClause j cl) x ↔
      (∃ l ∈ cl, x = 2*l.1) ∨ (cl.length = 4 ∧ x = fresh j) := by
  have short (l : Clause) : Mentioned [l.map liftLit] x ↔ ∃ y ∈ l, x = 2*y.1 := by
    simp only [Mentioned,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.map_map,List.mem_map,Function.comp_def,liftLit]
    exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))
  match cl with
  | [] | [_] | [_,_] | [_,_,_] | _::_::_::_::_::_ =>
    simp only [splitClause,short]
    simp
  | [a,b,c,d] =>
    simp only [splitClause,Mentioned,liftLit,List.flatMap_cons,List.flatMap_nil,List.map_cons,
      List.map_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,
      List.length_cons,List.length_nil,true_and,exists_eq_or_imp,exists_eq_left]
    tauto

theorem mentioned_splitCNF (F : CNF) (x : ℕ) :
    Mentioned (splitCNF F) x ↔
      (∃ i, Mentioned F i ∧ x = 2*i) ∨
        (∃ j < F.length, (F[j]?.getD []).length = 4 ∧ x = fresh j) := by
  have hstart : Mentioned (splitCNF F) x ↔
      ∃ j < F.length, Mentioned (splitClause j (F[j]?.getD [])) x := by
    simp only [Mentioned,splitCNF,List.flatMap_assoc,List.mem_flatMap,List.mem_range]
  rw [hstart]
  constructor
  · rintro ⟨j,hj,hm⟩
    rcases (mentioned_splitClause ..).mp hm with ⟨l,hl,rfl⟩ | ⟨hn,rfl⟩
    · have hc : F[j]?.getD [] ∈ F := by
        simpa [List.getElem?_eq_getElem hj] using List.getElem_mem hj
      exact Or.inl ⟨l.1,mentioned_of_clause hc hl,rfl⟩
    · exact Or.inr ⟨j,hj,hn,rfl⟩
  · rintro (⟨i,hi,rfl⟩ | ⟨j,hj,hn,rfl⟩)
    · unfold Mentioned at hi
      obtain ⟨cl,hcl,hm⟩ := List.mem_flatMap.mp hi
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm
      obtain ⟨j,hj,rfl⟩ := index_cover F hcl
      exact ⟨j,hj,(mentioned_splitClause ..).mpr (Or.inl ⟨l,hl,rfl⟩)⟩
    · exact ⟨j,hj,(mentioned_splitClause ..).mpr (Or.inr ⟨hn,rfl⟩)⟩


open PEqualNP.Outside.OneHot (Models extend eval_restrict eval_ext)

def fill (F : CNF) (σ : Assignment) : Assignment := fun x =>
  if x % 2 = 0 then σ (x / 2)
  else ((F[x / 2]?.getD []).take 2).any (Literal.eval σ)

theorem fill_even (F : CNF) (σ : Assignment) (i : ℕ) :
    fill F σ (2*i) = σ i := by
  unfold fill
  rw [if_pos (by omega), show 2*i/2=i by omega]

theorem fill_odd (F : CNF) (σ : Assignment) (j : ℕ) :
    fill F σ (fresh j) = ((F[j]?.getD []).take 2).any (Literal.eval σ) := by
  unfold fill fresh
  rw [if_neg (by omega), show (2*j+1)/2=j by omega]

theorem eval_fill (F : CNF) (σ : Assignment) :
    CNF.eval (fill F σ) (splitCNF F) = true ↔ CNF.eval σ F = true := by
  rw [splitCNF_ok, show (fun i => fill F σ (2*i)) = σ from funext (fill_even F σ)]
  simp only [fill_odd, implies_true, and_true]

def liftModel (F : CNF) (a : Models F) : Models (splitCNF F) :=
  ⟨fun i => fill F (extend F a.1) i.1,
    (eval_restrict ..).trans ((eval_fill ..).mpr a.2)⟩

def projectModel (F : CNF) (b : Models (splitCNF F)) : Models F := by
  let σ : Assignment := fun i => extend (splitCNF F) b.1 (2*i)
  refine ⟨fun i => σ i.1, (eval_restrict ..).trans ?_⟩
  exact ((splitCNF_ok ..).mp b.2).1

theorem project_eq (F : CNF) (b : Models (splitCNF F)) {i : ℕ} (hi : Mentioned F i) :
    extend F (projectModel F b).1 i = extend (splitCNF F) b.1 (2*i) := by
  exact dite_eq_left hi

theorem project_lift (F : CNF) (a : Models F) : projectModel F (liftModel F a) = a := by
  apply Subtype.ext
  funext i
  have hmem : Mentioned (splitCNF F) (2*i.1) :=
    (mentioned_splitCNF F _).mpr (Or.inl ⟨i.1,i.2,rfl⟩)
  change extend (splitCNF F) (liftModel F a).1 (2*i.1) = a.1 i
  have hread : extend (splitCNF F) (liftModel F a).1 (2*i.1) =
      (liftModel F a).1 ⟨2*i.1,hmem⟩ := dite_eq_left hmem
  rw [hread]
  change fill F (extend F a.1) (2*i.1) = a.1 i
  rw [fill_even]
  exact dite_eq_left i.2

theorem lift_project (F : CNF) (b : Models (splitCNF F)) : liftModel F (projectModel F b) = b := by
  apply Subtype.ext
  funext x
  let σ := extend (splitCNF F) b.1
  have hval : σ x.1 = b.1 x := dite_eq_left x.2
  change fill F (extend F (projectModel F b).1) x.1 = b.1 x
  rw [← hval]
  obtain ⟨i,hi,hx⟩ | ⟨j,hj,hfour,hx⟩ := (mentioned_splitCNF F _).mp x.2
  · rw [hx,fill_even,project_eq F b hi]
  · rw [hx,fill_odd,((splitCNF_ok σ F).mp b.2).2 j hj hfour]
    let cl := F[j]?.getD []
    have hc : cl ∈ F := by
      simpa [cl,List.getElem?_eq_getElem hj] using List.getElem_mem hj
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    exact exists_congr (fun l => and_congr_right (fun hl => by
      have hm : l ∈ cl := List.mem_of_mem_take hl
      simp only [Literal.eval, project_eq F b (mentioned_of_clause hc hm), σ]))

def splitEquiv (F : CNF) : Models F ≃ Models (splitCNF F) where
  toFun := liftModel F
  invFun := projectModel F
  left_inv := project_lift F
  right_inv := lift_project F

end PEqualNP.Outside.CNFWidth
