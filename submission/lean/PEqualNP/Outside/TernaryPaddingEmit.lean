import PEqualNP.Outside.TernaryPaddingDegree
import PEqualNP.Outside.MeasuredClauseSplit

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.SatCodePrimitives (cptl)
open PEqualNP.Outside.CNFWidth (Word oddLit oddLit_cpt oddLit_len oddLit_enc evenLit evenLit_cpt evenLit_len evenLit_enc)
open PEqualNP.Library.SearchHelpers.S2D (incB bits_succ incB_length cpt_incB)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def plusBits (k : ℕ) (s : Word) : Word := incB^[k] s

theorem plusBits_cpt (k : ℕ) : CPT (plusBits k) := by
  induction k with
  | zero => exact cpt_id
  | succ k ih =>
    exact cptl (cpt_comp ih cpt_incB) (fun s => by simp [plusBits,Function.iterate_succ_apply'])

theorem plusBits_enc (k n : ℕ) : plusBits k n.bits = (n+k).bits := by
  induction k with
  | zero => simp [plusBits]
  | succ k ih =>
    simp only [plusBits,Function.iterate_succ_apply'] at ih ⊢
    rw [ih,← bits_succ]
    rfl

theorem plusBits_len (k : ℕ) (s : Word) : (plusBits k s).length ≤ s.length+k := by
  induction k with
  | zero => simp [plusBits]
  | succ k ih =>
    have hh := incB_length (plusBits k s)
    simp only [plusBits,Function.iterate_succ_apply'] at hh ih ⊢
    omega

def localFormula (m : ℕ) : CNF :=
  [(List.range m).map (fun i => (4*i,true))] ++
    (List.range m).flatMap (fun i => gadget.map (List.map (lift (fun v => 4*i+v))))

def localWord (F : CNF) (b : Word) : Word :=
  F.flatMap (fun c => c.flatMap (fun l => oddLit l.2 (plusBits l.1 b)) ++ [false,false])

theorem localWord_cpt (F : CNF) : CPT (localWord F) := by
  have hc (c : Clause) : CPT (fun b => c.flatMap (fun l => oddLit l.2 (plusBits l.1 b))) := by
    induction c with
    | nil => exact cpt_const []
    | cons l c ih => exact cpt_app2 (cpt_comp (plusBits_cpt l.1) (oddLit_cpt l.2)) ih
  induction F with
  | nil => exact cpt_const []
  | cons c F ih => exact cpt_app2 (cpt_app2 (hc c) (cpt_const [false,false])) ih

theorem localWord_enc (F : CNF) (n : ℕ) :
    localWord F n.bits = encodeCNF (F.map (List.map (lift (fun i => 2*(n+i)+1)))) := by
  simp [localWord,encodeCNF,encodeClause,List.flatMap_map,Function.comp_def,plusBits_enc,
    oddLit_enc,lift,PEqualNP.Outside.CNFWidth.fresh]

theorem localWord_len (F : CNF) : ∃ a, ∀ b, (localWord F b).length ≤ a*(b.length+1) := by
  have hc : ∀ c : Clause, ∃ a, ∀ b,
      (c.flatMap (fun l => oddLit l.2 (plusBits l.1 b))).length ≤ a*(b.length+1) := by
    intro c
    induction c with
    | nil => exact ⟨0,by simp⟩
    | cons l c ih =>
      obtain ⟨a,ha⟩ := ih
      refine ⟨a+2*l.1+8,fun b => ?_⟩
      have hh := plusBits_len l.1 b
      have ht := ha b
      simp only [List.flatMap_cons,List.length_append,oddLit_len]
      calc
        _ ≤ a*(b.length+1)+(2*b.length+2*l.1+6) := by omega
        _ ≤ (a+2*l.1+8)*(b.length+1) := by
          rw [Nat.add_mul,Nat.add_mul]
          have h1 : 2*l.1 ≤ (2*l.1)*(b.length+1) := by
            simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2*l.1) (show 1 ≤ b.length+1 by omega)
          simp only [Nat.mul_add,Nat.mul_one]
          omega
  induction F with
  | nil => exact ⟨0,by simp [localWord]⟩
  | cons c F ih =>
    obtain ⟨a,ha⟩ := hc c
    obtain ⟨d,hd⟩ := ih
    refine ⟨a+d+2,fun b => ?_⟩
    have h1 := ha b
    have h2 := hd b
    change (c.flatMap (fun l => oddLit l.2 (plusBits l.1 b)) ++ [false,false] ++ localWord F b).length ≤ _
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_mul]
    omega

theorem local_tail (m j : ℕ) (c : Clause) (hm : m = missing c) :
    (localFormula m).map (List.map (lift (fun i => 2*(12*j+i)+1))) =
      [added j c] ++ (List.range (missing c)).flatMap (place j) := by
  subst m
  simp only [localFormula,List.map_append,List.map_cons,List.map_nil,List.map_map,
    List.map_flatMap,Function.comp_def,added,place,lift,fresh,Nat.add_zero]
  rfl

end PEqualNP.Outside.TernaryGadget
