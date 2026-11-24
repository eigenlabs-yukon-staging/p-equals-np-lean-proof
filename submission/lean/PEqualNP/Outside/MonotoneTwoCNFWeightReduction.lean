import PEqualNP.Outside.ClauseOccurrenceConflict
import Mathlib.Data.Finset.Prod

namespace PEqualNP.Outside.MonotoneTwoCNFWeightReduction

open PEqualNP.Search
open PEqualNP.Outside.ClauseOccurrenceConflict

def vertex {φ : CNF} (tag : Occurrence φ ↪ ℕ) (a : Occurrence φ) : ℕ :=
  2 * tag a + 1

def rowMarker {φ : CNF} (i : Row φ) : ℕ := 2 * (i.val + 1)

theorem vertex_ne_zero {φ : CNF} (tag : Occurrence φ ↪ ℕ) (a : Occurrence φ) :
    vertex tag a ≠ 0 := by
  unfold vertex
  omega

theorem marker_ne_zero {φ : CNF} (i : Row φ) : rowMarker i ≠ 0 := by
  unfold rowMarker
  omega

theorem vertex_ne_marker {φ : CNF} (tag : Occurrence φ ↪ ℕ)
    (a : Occurrence φ) (i : Row φ) : vertex tag a ≠ rowMarker i := by
  unfold vertex rowMarker
  omega

def vertexEmbedding {φ : CNF} (tag : Occurrence φ ↪ ℕ) : Occurrence φ ↪ ℕ :=
  ⟨vertex tag, fun a b h => tag.injective (by unfold vertex at h; omega)⟩

def rowEmbedding (φ : CNF) : Row φ ↪ ℕ :=
  ⟨rowMarker, fun a b h => Fin.ext (by unfold rowMarker at h; omega)⟩

def unit (i : ℕ) : Clause := [(i, true)]

def edge (i j : ℕ) : Clause := [(i, true), (j, true)]

noncomputable def graphCNF {φ : CNF} (tag : Occurrence φ ↪ ℕ) : CNF :=
  open Classical in
  unit 0 ::
    ((Finset.univ : Finset (Row φ)).toList.map (fun i => unit (rowMarker i)) ++
    (Finset.univ : Finset (Occurrence φ)).toList.map (fun a => edge 0 (vertex tag a)) ++
    ((Finset.univ : Finset (Occurrence φ × Occurrence φ)).filter
      (fun q => conflict q.1 q.2)).toList.map (fun q => edge (vertex tag q.1) (vertex tag q.2)))

theorem graph_shape {φ : CNF} (tag : Occurrence φ ↪ ℕ) :
    ∀ c ∈ graphCNF tag, c.length ≤ 2 ∧ c.all Prod.snd = true := by
  classical
  intro c hc
  simp only [graphCNF, List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | h
  · decide
  · rcases h with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp [unit, edge]

theorem graph_eval {φ : CNF} (tag : Occurrence φ ↪ ℕ) (σ : Assignment) :
    CNF.eval σ (graphCNF tag) = true ↔
      σ 0 = true ∧ (∀ i : Row φ, σ (rowMarker i) = true) ∧
      ∀ a b : Occurrence φ, conflict a b → σ (vertex tag a) = true ∨ σ (vertex tag b) = true := by
  classical
  simp [graphCNF, CNF.eval, Clause.eval, Literal.eval, unit, edge, List.all_append,
    List.all_map, Bool.and_eq_true, List.all_eq_true, and_assoc, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, Function.comp_def]
  intro h0 _ _ x
  exact Or.inl h0

def weight (φ : CNF) (σ : Assignment) : ℕ :=
  ((φ.flatMap fun c => c.map Prod.fst).toFinset.filter (fun i => σ i = true)).card

def occurring (φ : CNF) : Finset ℕ := (φ.flatMap fun c => c.map Prod.fst).toFinset

theorem occurring_graph {φ : CNF} (tag : Occurrence φ ↪ ℕ) :
    occurring (graphCNF tag) =
      insert 0 (((Finset.univ : Finset (Row φ)).map (rowEmbedding φ)) ∪
        ((Finset.univ : Finset (Occurrence φ)).map (vertexEmbedding tag))) := by
  classical
  ext v
  simp only [occurring, graphCNF, List.flatMap_cons, unit, List.map_cons, List.map_nil,
    List.singleton_append, List.flatMap_append, List.mem_toFinset, List.mem_cons, List.mem_append,
    Finset.mem_insert, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | (h | h) | h)
    · exact Or.inl rfl
    · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp h
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      have he : v = rowMarker i := by simpa [unit] using hv
      exact Or.inr (Or.inl ⟨i, he.symm⟩)
    · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp h
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
      rcases (by simpa [edge] using hv : v = 0 ∨ v = vertex tag a) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨a, rfl⟩)
    · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp h
      obtain ⟨⟨a,b⟩, _, rfl⟩ := List.mem_map.mp hc
      rcases (by simpa [edge] using hv : v = vertex tag a ∨ v = vertex tag b) with rfl | rfl
      · exact Or.inr (Or.inr ⟨a, rfl⟩)
      · exact Or.inr (Or.inr ⟨b, rfl⟩)
  · rintro (rfl | ⟨i, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inl (List.mem_flatMap.mpr
        ⟨unit (rowMarker i), List.mem_map.mpr ⟨i, by simp, rfl⟩, by change rowMarker i ∈ [rowMarker i]; simp⟩)))
    · exact Or.inr (Or.inl (Or.inr (List.mem_flatMap.mpr
        ⟨edge 0 (vertex tag a), List.mem_map.mpr ⟨a, by simp, rfl⟩, by change vertex tag a ∈ [0, vertex tag a]; simp⟩)))

def selected {φ : CNF} (tag : Occurrence φ ↪ ℕ) (σ : Assignment) : Finset (Occurrence φ) :=
  open Classical in
  Finset.univ.filter (fun a => σ (vertex tag a) = false)

theorem weight_eq {φ : CNF} (tag : Occurrence φ ↪ ℕ) (σ : Assignment)
    (h0 : σ 0 = true) (hr : ∀ i : Row φ, σ (rowMarker i) = true) :
    weight (graphCNF tag) σ + (selected tag σ).card =
      (Fintype.card (Occurrence φ)) + φ.length + 1 := by
  classical
  let rows := (Finset.univ : Finset (Row φ)).map (rowEmbedding φ)
  let yes : Finset (Occurrence φ) := Finset.univ.filter (fun a => σ (vertex tag a) = true)
  let vertices := yes.map (vertexEmbedding tag)
  have hdis : Disjoint rows vertices := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hk
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hj
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hk
    exact vertex_ne_marker tag a i (ha.trans hi.symm)
  have hn : 0 ∉ rows ∪ vertices := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      exact marker_ne_zero i hi
    · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
      exact vertex_ne_zero tag a ha
  have hset : (occurring (graphCNF tag)).filter (fun i => σ i = true) =
      insert 0 (rows ∪ vertices) := by
    rw [occurring_graph]
    ext j
    simp only [rows, vertices, yes, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨rfl | ⟨i, rfl⟩ | ⟨a, rfl⟩, hj⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨i, rfl⟩)
      · exact Or.inr (Or.inr ⟨a, hj, rfl⟩)
    · rintro (rfl | ⟨i, rfl⟩ | ⟨a, h, rfl⟩)
      · exact ⟨Or.inl rfl, h0⟩
      · exact ⟨Or.inr (Or.inl ⟨i, rfl⟩), hr i⟩
      · exact ⟨Or.inr (Or.inr ⟨a, rfl⟩), h⟩
  have hpart : yes.card + (selected tag σ).card = Fintype.card (Occurrence φ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Occurrence φ))) (p := fun a => σ (vertex tag a) = true)
    simpa [yes, selected, Bool.not_eq_true] using h
  change ((occurring (graphCNF tag)).filter (fun i => σ i = true)).card + _ = _
  rw [hset, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hdis]
  simp only [rows, vertices, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  omega

noncomputable def modelFromSet {φ : CNF} (tag : Occurrence φ ↪ ℕ)
    (s : Finset (Occurrence φ)) : Assignment := fun i =>
  open Classical in
  decide (∀ a ∈ s, i ≠ vertex tag a)

theorem modelFromSet_vertex {φ : CNF} (tag : Occurrence φ ↪ ℕ) (s : Finset (Occurrence φ))
    (a : Occurrence φ) : modelFromSet tag s (vertex tag a) = true ↔ a ∉ s := by
  classical
  simp only [modelFromSet, decide_eq_true_eq]
  constructor
  · exact fun h ha => h a ha rfl
  · intro h b hb he
    exact h ((vertexEmbedding tag).injective he ▸ hb)

theorem fromSet_satisfies {φ : CNF} (tag : Occurrence φ ↪ ℕ) (s : Finset (Occurrence φ))
    (hs : independent s) : CNF.eval (modelFromSet tag s) (graphCNF tag) = true := by
  classical
  rw [graph_eval]
  refine ⟨?_, ?_, ?_⟩
  · simp only [modelFromSet, decide_eq_true_eq]
    exact fun a _ => Ne.symm (vertex_ne_zero tag a)
  · intro i
    simp only [modelFromSet, decide_eq_true_eq]
    exact fun a _ => Ne.symm (vertex_ne_marker tag a i)
  · intro a b h
    rw [modelFromSet_vertex, modelFromSet_vertex]
    by_cases ha : a ∈ s
    · exact Or.inr (fun hb => hs a ha b hb h)
    · exact Or.inl ha

theorem selected_fromSet {φ : CNF} (tag : Occurrence φ ↪ ℕ) (s : Finset (Occurrence φ)) :
    selected tag (modelFromSet tag s) = s := by
  classical
  ext a
  simp [selected, ← Bool.not_eq_true, modelFromSet_vertex]

theorem weight_iff_sat (φ : CNF) (tag : Occurrence φ ↪ ℕ) :
    (∃ σ : Assignment, CNF.eval σ (graphCNF tag) = true ∧
      weight (graphCNF tag) σ ≤ Fintype.card (Occurrence φ) + 1) ↔ Satisfiable φ := by
  classical
  constructor
  · rintro ⟨σ, he, hw⟩
    obtain ⟨h0, hr, hc⟩ := (graph_eval tag σ).mp he
    have hcard := weight_eq tag σ h0 hr
    apply sat_of_independent (s := selected tag σ) _ (by omega)
    intro a ha b hb hconf
    have h := hc a b hconf
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp [ha, hb] at h
  · intro h
    obtain ⟨s, hs, hcard⟩ := independent_of_sat h
    let σ := modelFromSet tag s
    have hsat := fromSet_satisfies tag s hs
    obtain ⟨h0, hr, _⟩ := (graph_eval tag σ).mp hsat
    have hw := weight_eq tag σ h0 hr
    rw [show selected tag σ = s from selected_fromSet tag s, hcard] at hw
    exact ⟨σ, hsat, by omega⟩

end PEqualNP.Outside.MonotoneTwoCNFWeightReduction
