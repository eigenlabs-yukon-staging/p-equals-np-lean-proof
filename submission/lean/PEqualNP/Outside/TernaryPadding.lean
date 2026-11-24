import PEqualNP.Outside.TernaryNormalize
import PEqualNP.Outside.TernaryFalseGadget

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Search

def lift (f : ℕ → ℕ) (l : Literal) : Literal := (f l.1,l.2)
def old (v : ℕ) : ℕ := 2*v
def fresh (j i v : ℕ) : ℕ := 2*(12*j+4*i+v)+1

def place (j i : ℕ) : CNF := gadget.map (List.map (lift (fresh j i)))
def missing (cl : Clause) : ℕ := 3-cl.length
def added (j : ℕ) (cl : Clause) : Clause :=
  (List.range (missing cl)).map (fun i => (fresh j i 0,true))
def block (j : ℕ) (cl : Clause) : CNF :=
  [cl.map (lift old) ++ added j cl] ++ (List.range (missing cl)).flatMap (place j)

def padFrom (j : ℕ) : CNF → CNF
  | [] => []
  | c::F => block j c ++ padFrom (j+1) F

theorem rename_clause (σ : Assignment) (f : ℕ → ℕ) (cl : Clause) :
    Clause.eval σ (cl.map (lift f)) = Clause.eval (σ ∘ f) cl := by
  simp only [Clause.eval,List.any_map]
  rfl

theorem rename_formula (σ : Assignment) (f : ℕ → ℕ) (F : CNF) :
    CNF.eval σ (F.map (List.map (lift f))) = CNF.eval (σ ∘ f) F := by
  simp only [CNF.eval,List.all_map,Function.comp_def,rename_clause]

theorem place_forces (σ : Assignment) (j i : ℕ) (h : CNF.eval σ (place j i) = true) :
    σ (fresh j i 0) = false := by
  rw [place,rename_formula] at h
  exact forced _ h

theorem block_sound (σ : Assignment) (j : ℕ) (cl : Clause)
    (h : CNF.eval σ (block j cl) = true) :
    Clause.eval (σ ∘ old) cl = true := by
  have hforced : ∀ i < missing cl, σ (fresh j i 0) = false := by
    intro i hi
    apply place_forces σ
    simp only [CNF.eval,List.all_eq_true] at h ⊢
    intro c hc
    exact h c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩))
  have hm : Clause.eval σ (cl.map (lift old) ++ added j cl) = true :=
    List.all_eq_true.mp h _ (List.mem_append_left _ (by simp))
  have hn : Clause.eval σ (added j cl) = false := by
    cases e : Clause.eval σ (added j cl)
    · rfl
    · obtain ⟨l,hl,he⟩ := List.any_eq_true.mp e
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
      simp [Literal.eval,hforced i (List.mem_range.mp hi)] at he
  have he : (Clause.eval σ (cl.map (lift old)) || Clause.eval σ (added j cl)) = true := by
    simpa only [Clause.eval,List.any_append] using hm
  rw [hn,Bool.or_false,rename_clause] at he
  exact he

def extend (σ : Assignment) : Assignment :=
  fun v => if v % 2 = 0 then σ (v/2) else false

theorem extend_old (σ : Assignment) (v : ℕ) : extend σ (old v) = σ v := by
  unfold extend old
  rw [if_pos (by omega),show 2*v/2=v by omega]

theorem extend_new (σ : Assignment) (j i v : ℕ) : extend σ (fresh j i v) = false := by
  unfold extend fresh
  rw [if_neg (by omega)]

theorem block_complete (σ : Assignment) (j : ℕ) (cl : Clause)
    (h : Clause.eval σ cl = true) : CNF.eval (extend σ) (block j cl) = true := by
  simp only [CNF.eval,List.all_eq_true,block,List.mem_append,List.mem_singleton,List.mem_flatMap]
  intro c hc
  rcases hc with rfl | ⟨i,hi,hc⟩
  · have he : extend σ ∘ old = σ := funext (extend_old σ)
    have h' := rename_clause (extend σ) old cl
    rw [he,h] at h'
    simp only [Clause.eval,List.any_append,show (cl.map (lift old)).any (Literal.eval (extend σ)) = true from h',
      Bool.true_or]
  · have h0 : extend σ ∘ fresh j i = fun _ => false := funext (extend_new σ j i)
    have hh : CNF.eval (extend σ) (place j i) = true := by
      rw [place,rename_formula,h0]
      exact zero_model
    exact List.all_eq_true.mp hh _ hc

theorem pad_sat (F : CNF) (j : ℕ) : Satisfiable (padFrom j F) ↔ Satisfiable F := by
  constructor
  · rintro ⟨σ,h⟩
    refine ⟨σ ∘ old, ?_⟩
    induction F generalizing j with
    | nil => rfl
    | cons c F ih =>
      have he : CNF.eval σ (block j c) = true ∧ CNF.eval σ (padFrom (j+1) F) = true := by
        simpa only [padFrom,CNF.eval,List.all_append,Bool.and_eq_true_iff] using h
      exact Bool.and_eq_true_iff.mpr ⟨block_sound σ j c he.1,ih (j+1) he.2⟩
  · rintro ⟨σ,h⟩
    refine ⟨extend σ, ?_⟩
    induction F generalizing j with
    | nil => rfl
    | cons c F ih =>
      have h' : Clause.eval σ c = true ∧ CNF.eval σ F = true := by
        simpa only [CNF.eval,List.all_cons,Bool.and_eq_true_iff] using h
      simpa only [padFrom,CNF.eval,List.all_append,Bool.and_eq_true_iff] using
        And.intro (block_complete σ j c h'.1) (ih (j+1) h'.2)


theorem fresh_local_inj (j i : ℕ) : Function.Injective (fresh j i) := by
  intro v w h
  unfold fresh at h
  omega

theorem old_inj : Function.Injective old := by
  intro a b h
  unfold old at h
  omega

theorem distinct_slot (j : ℕ) : Function.Injective (fun i => fresh j i 0) := by
  intro a b h
  change fresh j a 0 = fresh j b 0 at h
  unfold fresh at h
  omega

theorem place_shape (j i : ℕ) (c : Clause) (hc : c ∈ place j i) :
    c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have h := shape d hd
  constructor
  · simpa only [List.length_map] using h.1
  · simpa only [List.map_map,Function.comp_def,lift] using h.2.1.map (fresh_local_inj j i)

theorem added_ids (j : ℕ) (cl : Clause) :
    (added j cl).map Prod.fst = (List.range (missing cl)).map (fun i => fresh j i 0) := by
  simp [added,List.map_map,Function.comp_def]

theorem lifted_ids (f : ℕ → ℕ) (cl : Clause) :
    (cl.map (lift f)).map Prod.fst = (cl.map Prod.fst).map f := by
  simp [lift,List.map_map,Function.comp_def]

theorem padding_shape (j : ℕ) (cl : Clause) (h : cl.length ≤ 3)
    (hd : (cl.map Prod.fst).Nodup) :
    (cl.map (lift old) ++ added j cl).length = 3 ∧
      ((cl.map (lift old) ++ added j cl).map Prod.fst).Nodup := by
  constructor
  · simp only [List.length_append,List.length_map,added,List.length_range,missing]
    omega
  · rw [List.map_append,lifted_ids,added_ids,List.nodup_append]
    refine ⟨hd.map old_inj,(List.nodup_range ..).map (distinct_slot j),?_⟩
    intro n hn m hm hnm
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
    unfold old fresh at hnm
    omega

theorem pad_shape (F : CNF) (j : ℕ)
    (h : ∀ c ∈ F, c.length ≤ 3 ∧ (c.map Prod.fst).Nodup) :
    ∀ c ∈ padFrom j F, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  induction F generalizing j with
  | nil => simp [padFrom]
  | cons c F ih =>
    have hc := h c (List.mem_cons_self ..)
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · have he := List.mem_singleton.mp ha
        subst a
        exact padding_shape j c hc.1 hc.2
      · obtain ⟨i,_,ha⟩ := List.mem_flatMap.mp ha
        exact place_shape j i a ha
    · exact ih (j+1) (fun d hd => h d (List.mem_cons_of_mem _ hd)) a ha

end PEqualNP.Outside.TernaryGadget
