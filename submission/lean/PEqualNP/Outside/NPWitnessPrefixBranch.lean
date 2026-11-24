import PEqualNP.Outside.PrefixDecideHelpers
import PEqualNP.Outside.RecordPairScan

namespace PEqualNP.Outside.NPWitnessPrefixBranch

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.PrefixDecideHelpers (Word Rel good extensions eval_mono_nat cpt_test)
open PEqualNP.Outside.RecordPairScan (wire)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def done (verify : Word × Word → Bool) (p : Polynomial ℕ) (z : Word) : Bool :=
  decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)

theorem done_spec (R : Rel) (p : Polynomial ℕ) (verify : Word × Word → Bool)
    (hv : ∀ q, q ∈ R ↔ verify q = true) (z : Word) :
    done verify p z = true ↔ good R p (unpairB z).1 (unpairB z).2 := by
  simp only [done, good, hv, Prod.mk.eta, Bool.and_eq_true, decide_eq_true_eq]

def child (z : Word) (b : Bool) : Word := pairB (unpairB z).1 ((unpairB z).2 ++ [b])

def children (test : Word → Bool) (z : Word) : List Word :=
  if test z = true then [z] else [child z false,child z true]

theorem children_cpt (test : Word → Bool)
    (ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool test) :
    CPT (fun z => wire (children test z)) := by
  have hchild (b : Bool) : CPT (fun z => child z b) :=
    cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [b]))
  have hstay := cpt_pairB2 cpt_id (cpt_const [])
  have hgo := cpt_pairB2 (hchild false) (cpt_pairB2 (hchild true) (cpt_const []))
  exact cptl (cpt_sel (cpt_bitFlag ht) hgo hstay) (fun z => by cases h : test z <;>
    simp [children,h,bflag,sel,wire])

theorem children_growth (test : Word → Bool) (z y : Word) (hy : y ∈ children test z) :
    y.length ≤ z.length + 2 := by
  unfold children at hy
  split at hy
  · simp at hy
    subst y
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have h := unpairB_length z
    rcases hy with rfl | rfl <;> simp only [child,pairB_length,List.length_append,List.length_singleton] <;> omega

theorem extensions_child (R : Rel) (p : Polynomial ℕ) (z : Word) (b : Bool) :
    child z b ∈ extensions R p ↔
      ∃ t : Word, good R p (unpairB z).1 ((unpairB z).2 ++ b :: t) := by
  change (∃ t : Word, good R p (unpairB (child z b)).1 ((unpairB (child z b)).2 ++ t)) ↔ _
  simp [child, unpairB_pairB, List.append_assoc]

theorem extension_branch (R : Rel) (p : Polynomial ℕ) (verify : Word × Word → Bool)
    (hv : ∀ q, q ∈ R ↔ verify q = true) (z : Word) :
    z ∈ extensions R p ↔ ∃ y ∈ children (done verify p) z, y ∈ extensions R p := by
  by_cases h : done verify p z = true
  · simp [children,h]
  · have hn : ¬good R p (unpairB z).1 (unpairB z).2 := fun hg => h ((done_spec R p verify hv z).mpr hg)
    have hch : children (done verify p) z = [child z false,child z true] := if_neg h
    rw [hch]
    constructor
    · rintro ⟨t,ht⟩
      cases t with
      | nil => exact False.elim (hn (by simpa using ht))
      | cons b t =>
        cases b
        · exact ⟨child z false, List.mem_cons_self, (extensions_child R p z false).mpr ⟨t,ht⟩⟩
        · exact ⟨child z true, by simp, (extensions_child R p z true).mpr ⟨t,ht⟩⟩
    · rintro ⟨y,hy,hgood⟩
      rcases List.mem_cons.mp hy with h | h
      · subst y
        obtain ⟨t,ht⟩ := (extensions_child R p z false).mp hgood
        exact ⟨false::t,ht⟩
      · have he := List.mem_singleton.mp h
        subst y
        obtain ⟨t,ht⟩ := (extensions_child R p z true).mp hgood
        exact ⟨true::t,ht⟩

theorem path (test : Word → Bool) (z y : Word) (n : ℕ)
    (hy : y ∈ (fun rs : List Word => rs.flatMap (children test))^[n] [z]) :
    (unpairB y).1 = (unpairB z).1 ∧
      (test y = true ∨ (unpairB z).2.length+n ≤ (unpairB y).2.length) := by
  induction n generalizing y with
  | zero =>
    change y ∈ [z] at hy
    simp only [List.mem_singleton] at hy
    subst y
    exact ⟨rfl,Or.inr (by simp)⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hy
    obtain ⟨s,hs,hsy⟩ := List.mem_flatMap.mp hy
    obtain ⟨hx,hlen⟩ := ih s hs
    by_cases ht : test s = true
    · simp [children,ht] at hsy
      subst y
      exact ⟨hx, Or.inl ht⟩
    · have hch : children test s = [child s false,child s true] := if_neg ht
      rw [hch] at hsy
      have hb := hlen.resolve_left ht
      have hchild (b : Bool) :
          (unpairB (child s b)).1 = (unpairB z).1 ∧
            (test (child s b) = true ∨ (unpairB z).2.length + (n+1) ≤
              (unpairB (child s b)).2.length) := by
        simp only [child,unpairB_pairB,List.length_append,List.length_singleton]
        exact ⟨hx, Or.inr (by omega)⟩
      rcases List.mem_cons.mp hsy with h | h
      · subst y
        exact hchild false
      · have he := List.mem_singleton.mp h
        subst y
        exact hchild true

theorem leaf (R : Rel) (p : Polynomial ℕ) (verify : Word × Word → Bool)
    (hv : ∀ q, q ∈ R ↔ verify q = true) (x y : Word)
    (hy : y ∈ (fun rs : List Word => rs.flatMap (children (done verify p)))^[p.eval x.length] [x]) :
    done verify p y = true ↔ y ∈ extensions R p := by
  constructor
  · intro h
    exact ⟨[], by simpa using (done_spec R p verify hv y).mp h⟩
  · intro h
    obtain ⟨hx,ht | hlen⟩ := path (done verify p) x y _ hy
    · exact ht
    · obtain ⟨t,hgood⟩ := h
      by_cases ht : t = []
      · subst t
        exact (done_spec R p verify hv y).mpr (by simpa using hgood)
      · have hw := hgood.1
        simp only [List.length_append,hx] at hw
        have hsrc : (unpairB x).1.length ≤ x.length := by have h := unpairB_length x; omega
        have hmono : p.eval (unpairB x).1.length ≤ p.eval x.length := eval_mono_nat p hsrc
        have hpos := List.length_pos_iff.mpr ht
        omega

end PEqualNP.Outside.NPWitnessPrefixBranch
