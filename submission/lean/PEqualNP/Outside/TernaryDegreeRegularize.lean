import PEqualNP.Outside.TernaryDegreeFillGadget
import PEqualNP.Outside.TernaryPaddingDegree

namespace PEqualNP.Outside.DegreeFill
open PEqualNP.Search
open PEqualNP.Outside.OccurrenceSplit (ids ids_append)
open PEqualNP.Outside.TernaryGadget
  (lift old old_inj lifted_ids ids_rename ids_flatMap rename_formula)

def slot (i k : ℕ) : ℕ := if k = 0 then 0 else 5*i+k

def template (n : ℕ) : CNF :=
  (List.range n).flatMap (fun i => gadget.map (List.map (lift (slot i))))

def embed (j v k : ℕ) : ℕ :=
  if k = 0 then old v else 2*(15*j+k)+1

def block (j v m : ℕ) : CNF := (template m).map (List.map (lift (embed j v)))

def fillFrom (F : CNF) (j : ℕ) : List ℕ → CNF
  | [] => []
  | v::vs => block j v (4-(ids F).count v) ++ fillFrom F (j+1) vs

def regular (F : CNF) : CNF :=
  F.map (List.map (lift old)) ++ fillFrom F 0 (ids F).dedup

theorem template_shape (m : ℕ) (hm : m ≤ 3) :
    ∀ c ∈ template m, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  interval_cases m <;> decide

theorem template_support (m : ℕ) (hm : m ≤ 3) :
    ∀ k ∈ ids (template m), k ≤ 15 := by
  interval_cases m <;> decide

theorem template_terminal (m : ℕ) (hm : m ≤ 3) : (ids (template m)).count 0 = m := by
  interval_cases m <;> decide

theorem template_internal (m : ℕ) (hm : m ≤ 3) :
    ∀ k ∈ ids (template m), k ≠ 0 → (ids (template m)).count k = 4 := by
  interval_cases m <;> decide

theorem embed_inj (j v : ℕ) : Function.Injective (embed j v) := by
  intro a b h
  unfold embed old at h
  split at h <;> split at h <;> omega

theorem block_shape (j v m : ℕ) (hm : m ≤ 3) :
    ∀ c ∈ block j v m, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  intro c hc
  obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hc
  obtain ⟨hL,hN⟩ := template_shape m hm cl hcl
  rw [List.length_map,lifted_ids]
  exact ⟨hL,hN.map (embed_inj j v)⟩

theorem block_support (j v m w : ℕ) (hm : m ≤ 3) (hw : w ∈ ids (block j v m)) :
    w = old v ∨ ∃ k, 0 < k ∧ k ≤ 15 ∧ w = 2*(15*j+k)+1 := by
  unfold block at hw
  rw [ids_rename] at hw
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
  by_cases hz : k = 0
  · exact Or.inl (by simp [embed,hz])
  · exact Or.inr ⟨k,Nat.pos_of_ne_zero hz,template_support m hm _ hk,by simp [embed,hz]⟩

theorem block_count_old (j v m x : ℕ) (hm : m ≤ 3) :
    (ids (block j v m)).count (old x) = if v = x then m else 0 := by
  by_cases he : v = x
  · subst x
    rw [if_pos rfl,block,ids_rename,← show embed j v 0 = old v by rfl,
      List.count_map_of_injective _ _ (embed_inj j v),template_terminal m hm]
  · rw [ite_eq_right he]
    apply List.count_eq_zero_of_not_mem
    intro h
    rcases block_support j v m (old x) hm h with h | ⟨k,_,_,h⟩
    · exact he (old_inj h.symm)
    · unfold old at h
      omega

theorem block_count_new (j v m w : ℕ) (hm : m ≤ 3) (hOdd : w % 2 = 1)
    (hw : w ∈ ids (block j v m)) : (ids (block j v m)).count w = 4 := by
  unfold block at *
  rw [ids_rename] at hw ⊢
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
  rw [List.count_map_of_injective _ _ (embed_inj j v)]
  apply template_internal m hm k hk
  intro hk0
  simp [hk0,embed,old] at hOdd

theorem allowance (F : CNF) (v : ℕ) (hv : v ∈ ids F) : 4-(ids F).count v ≤ 3 := by
  have h := List.count_pos_iff.mpr hv
  omega

theorem fill_support (F : CNF) (j : ℕ) (vs : List ℕ) (hvs : ∀ v ∈ vs, v ∈ ids F)
    (w : ℕ) (hOdd : w % 2 = 1) (hw : w ∈ ids (fillFrom F j vs)) :
    ∃ i, j ≤ i ∧ ∃ k, 0 < k ∧ k ≤ 15 ∧ w = 2*(15*i+k)+1 := by
  induction vs generalizing j with
  | nil => simp [fillFrom,ids] at hw
  | cons v vs ih =>
    rw [fillFrom,ids_append,List.mem_append] at hw
    rcases hw with hv | hw
    · rcases block_support j v _ w (allowance F v (hvs v (List.mem_cons_self ..))) hv with h | h
      · simp [h,old] at hOdd
      · exact ⟨j,Nat.le_refl _,h⟩
    · obtain ⟨i,hi,h⟩ := ih (j+1) (fun v hv => hvs v (List.mem_cons_of_mem _ hv)) hw
      exact ⟨i,by omega,h⟩

theorem fill_count_new (F : CNF) (j : ℕ) (vs : List ℕ) (hvs : ∀ v ∈ vs, v ∈ ids F)
    (w : ℕ) (hOdd : w % 2 = 1) (hw : w ∈ ids (fillFrom F j vs)) :
    (ids (fillFrom F j vs)).count w = 4 := by
  induction vs generalizing j with
  | nil => simp [fillFrom,ids] at hw
  | cons v vs ih =>
    rw [fillFrom,ids_append,List.count_append]
    have hv := allowance F v (hvs v (List.mem_cons_self ..))
    have htail : ∀ v ∈ vs, v ∈ ids F := fun x hx => hvs x (List.mem_cons_of_mem _ hx)
    by_cases h : w ∈ ids (block j v (4-(ids F).count v))
    · have hno : w ∉ ids (fillFrom F (j+1) vs) := by
        intro hmem
        obtain ⟨i,hi,k,hk,hk',he⟩ := fill_support F (j+1) vs htail w hOdd hmem
        rcases block_support j v _ w hv h with h | ⟨l,hl,hl',he'⟩
        · simp [h,old] at hOdd
        · omega
      rw [block_count_new j v _ w hv hOdd h,List.count_eq_zero_of_not_mem hno,Nat.add_zero]
    · rw [List.count_eq_zero_of_not_mem h,Nat.zero_add]
      rw [fillFrom,ids_append,List.mem_append] at hw
      exact ih _ htail (hw.resolve_left h)

theorem fill_count_old (F : CNF) (j : ℕ) (vs : List ℕ) (hN : vs.Nodup)
    (hvs : ∀ v ∈ vs, v ∈ ids F) (w : ℕ) :
    (ids (fillFrom F j vs)).count (old w) = if w ∈ vs then 4-(ids F).count w else 0 := by
  induction vs generalizing j with
  | nil => simp [fillFrom,ids]
  | cons v vs ih =>
    obtain ⟨hv,hN'⟩ := List.nodup_cons.mp hN
    rw [fillFrom,ids_append,List.count_append,
      block_count_old _ _ _ _ (allowance F v (hvs v (List.mem_cons_self ..))),
      ih (j+1) hN' (fun x hx => hvs x (List.mem_cons_of_mem _ hx))]
    by_cases he : w = v
    · subst w
      simp [hv]
    · by_cases hw : w ∈ vs <;> simp [he,Ne.symm he,hw]


theorem regular_shape (F : CNF)
    (hF : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup) :
    ∀ c ∈ regular F, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  have fill_shape (j : ℕ) (vs : List ℕ) (hvs : ∀ v ∈ vs, v ∈ ids F) :
      ∀ c ∈ fillFrom F j vs, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
    induction vs generalizing j with
    | nil => simp [fillFrom]
    | cons v vs ih =>
      intro c hc
      rw [fillFrom,List.mem_append] at hc
      rcases hc with hc | hc
      · exact block_shape j v _ (allowance F v (hvs v (List.mem_cons_self ..))) c hc
      · exact ih _ (fun v hv => hvs v (List.mem_cons_of_mem _ hv)) c hc
  intro c hc
  rw [regular,List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨cl,hcl,rfl⟩ := List.mem_map.mp hc
    obtain ⟨hL,hN⟩ := hF cl hcl
    rw [List.length_map,lifted_ids]
    exact ⟨hL,hN.map old_inj⟩
  · exact fill_shape 0 _ (fun _ => List.mem_dedup.mp) c hc

theorem regular_degree (F : CNF) (hF : ∀ v, (ids F).count v ≤ 4) :
    ∀ w ∈ ids (regular F), (ids (regular F)).count w = 4 := by
  intro w hw
  rw [regular,ids_append,ids_rename,List.count_append]
  rw [regular,ids_append,ids_rename,List.mem_append] at hw
  have hvs : ∀ v ∈ (ids F).dedup, v ∈ ids F := fun _ => List.mem_dedup.mp
  by_cases he : w % 2 = 0
  · have e : old (w/2) = w := by unfold old; omega
    rw [← e] at hw ⊢
    rw [List.count_map_of_injective _ _ old_inj,
      fill_count_old _ _ _ (List.nodup_dedup _) hvs]
    have hv : w/2 ∈ ids F := by
      rcases hw with hw | hw
      · obtain ⟨v,hv,h⟩ := List.mem_map.mp hw
        simpa [old_inj h] using hv
      · by_contra hh
        have hz := fill_count_old F 0 (ids F).dedup (List.nodup_dedup _) hvs (w/2)
        have hnot : w/2 ∉ (ids F).dedup := fun h => hh (List.mem_dedup.mp h)
        rw [ite_eq_right hnot] at hz
        have hpos := List.count_pos_iff.mpr hw
        omega
    rw [if_pos (List.mem_dedup.mpr hv)]
    exact Nat.add_sub_of_le (hF _)
  · have ho : w % 2 = 1 := by omega
    have hn : w ∉ (ids F).map old := by
      intro h
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
      simp [old] at ho
    rw [List.count_eq_zero_of_not_mem hn,Nat.zero_add]
    exact fill_count_new F 0 _ hvs w ho (hw.resolve_left hn)

def extend (a : Assignment) : Assignment := fun v => if v % 2 = 0 then a (v/2) else true

theorem extend_old (a : Assignment) (v : ℕ) : extend a (old v) = a v := by
  have h1 : old v % 2 = 0 := by unfold old; omega
  have h2 : old v / 2 = v := by unfold old; omega
  simp [extend,h1,h2]

theorem block_accepts (a : Assignment) (j v m : ℕ) :
    CNF.eval (extend a) (block j v m) = true := by
  rw [block,rename_formula]
  simp only [CNF.eval,List.all_eq_true]
  intro c hc
  unfold template at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hh : CNF.eval (extend a ∘ embed j v) (gadget.map (List.map (lift (slot i)))) = true := by
    rw [rename_formula]
    apply gadget_accepts
    intro k hk _
    have hs : 5*i+k ≠ 0 := by omega
    simp only [Function.comp_apply,slot,embed,if_neg (Nat.ne_of_gt hk),if_neg hs,extend]
    have hp : (2*(15*j+(5*i+k))+1)%2 ≠ 0 := by omega
    rw [if_neg hp]
  exact List.all_eq_true.mp hh c hc

theorem fill_accepts (a : Assignment) (F : CNF) (j : ℕ) (vs : List ℕ) :
    CNF.eval (extend a) (fillFrom F j vs) = true := by
  induction vs generalizing j with
  | nil => rfl
  | cons v vs ih =>
    simp only [fillFrom,CNF.eval,List.all_append,Bool.and_eq_true]
    exact ⟨block_accepts a j v _,ih _⟩

theorem regular_sat (F : CNF) : Satisfiable (regular F) ↔ Satisfiable F := by
  constructor
  · rintro ⟨a,ha⟩
    have h : (CNF.eval a (F.map (List.map (lift old))) &&
        CNF.eval a (fillFrom F 0 (ids F).dedup)) = true := by
      simpa only [regular,CNF.eval,List.all_append] using ha
    refine ⟨a ∘ old,?_⟩
    rw [← rename_formula]
    exact (Bool.and_eq_true_iff.mp h).1
  · rintro ⟨a,ha⟩
    refine ⟨extend a,?_⟩
    have he : extend a ∘ old = a := funext (extend_old a)
    have h := (rename_formula (extend a) old F).trans (congrArg (fun x => CNF.eval x F) he)
    simp only [regular,CNF.eval,List.all_append,Bool.and_eq_true]
    exact ⟨h.trans ha,fill_accepts a F 0 _⟩

end PEqualNP.Outside.DegreeFill

open PEqualNP.Search

theorem PEqualNP.Outside.TernaryDegreeRegularize :
    ∀ F : CNF,
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup) →
      (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 4) →
      ∃ G : CNF,
        (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        (∀ v ∈ G.flatMap (List.map Prod.fst), (G.flatMap (List.map Prod.fst)).count v = 4) ∧
        (Satisfiable G ↔ Satisfiable F) := by
  intro F hW hD
  open PEqualNP.Outside.DegreeFill in
  exact ⟨regular F,regular_shape F hW,regular_degree F hD,regular_sat F⟩
