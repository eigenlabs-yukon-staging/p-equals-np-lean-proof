import PEqualNP.Outside.SatCodeDecoder

namespace PEqualNP.Outside.SatCodeSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodeDecoder

abbrev Token := Option Literal

def support (φ : CNF) : List ℕ := (φ.flatten.map Prod.fst).eraseDups

def tokens (φ : CNF) : List Token :=
  φ.flatMap fun c => c.map some ++ [none]

def encToken : Token → Word
  | none => [false, false]
  | some l => encodeLiteral l

def encTokens (ts : List Token) : Word := ts.flatMap encToken

def ids (ts : List Token) : List ℕ := ts.filterMap (Option.map Prod.fst)

def newVars (s : List ℕ) : List Token → List ℕ
  | [] => []
  | none :: ts => newVars s ts
  | some l :: ts =>
    if l.1 ∈ s then newVars s ts else l.1 :: newVars (s ++ [l.1]) ts

theorem mem_newVars (i : ℕ) (s : List ℕ) (ts : List Token) :
    i ∈ newVars s ts ↔ i ∉ s ∧ i ∈ ids ts := by
  induction ts generalizing s with
  | nil => simp [newVars, ids]
  | cons t ts ih =>
    cases t with
    | none => simpa [newVars, ids] using ih s
    | some l =>
      by_cases h : l.1 ∈ s
      · simp only [newVars, h, ite_true, ih, ids, List.filterMap_cons_some, Option.map_some,
          List.mem_cons]
        grind
      · simp only [newVars, h, ite_false, List.mem_cons, ih, ids, List.filterMap_cons_some,
          Option.map_some, List.mem_append, List.mem_singleton]
        grind

theorem newVars_nodup (s : List ℕ) (ts : List Token) : (newVars s ts).Nodup := by
  induction ts generalizing s with
  | nil => simp [newVars]
  | cons t ts ih =>
    cases t with
    | none => exact ih s
    | some l =>
      by_cases h : l.1 ∈ s
      · simpa [newVars, h] using ih s
      · simp only [newVars, h, ite_false, List.nodup_cons, mem_newVars]
        exact ⟨fun hn => hn.1 (by simp), ih _⟩

theorem ids_tokens (φ : CNF) : ids (tokens φ) = φ.flatten.map Prod.fst := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have hm : (c.map some).filterMap (Option.map Prod.fst) = c.map Prod.fst := by
      induction c with
      | nil => rfl
      | cons l c ih => simp [ih]
    simpa [ids, tokens, List.filterMap_append, hm] using
      congrArg (fun z => c.map Prod.fst ++ z) ih

theorem encode_tokens (φ : CNF) : encTokens (tokens φ) = encodeCNF φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have hm : (c.map some).flatMap encToken = c.flatMap encodeLiteral := by
      induction c with
      | nil => rfl
      | cons l c ih => simp [encToken, ih]
    have h := congrArg (fun z => encodeClause c ++ z) ih
    simpa [encTokens, tokens, encodeCNF, encodeClause, encToken, List.flatMap_append, hm] using h

theorem vars_count_le (φ : CNF) : (newVars [] (tokens φ)).length ≤ (support φ).length := by
  apply List.Nodup.length_le_of_subset (newVars_nodup [] _)
  intro i hi
  have h := (mem_newVars i [] (tokens φ)).mp hi
  simpa [support, ids_tokens] using h.2

theorem count_newVars (φ : CNF) :
    (newVars [] (tokens φ)).length = (φ.flatten.map Prod.fst).toFinset.card := by
  rw [← List.toFinset_card_of_nodup (newVars_nodup [] _)]
  congr 1
  ext i
  simp [mem_newVars, ids_tokens]

theorem step_skip (r : Word) (s b w : Word) :
    step (pack ([false, false] ++ r) s b w) = pack r s b w := by
  simp [step, pack, item, remaining, seen, bits, output, headI, dropI, unpairB_pairB, sel]

theorem step_empty (s b w : Word) :
    step (pack [] s b w) = pack [] s b w := by
  simp [step, pack, item, remaining, seen, bits, output, headI, dropI, unpairB_pairB, sel]

theorem step_known (l : Literal) (r : Word) (s : List ℕ) (b w : Word) (h : l.1 ∈ s) :
    step (pack (encodeLiteral l ++ r) (s.flatMap vcode) b w) =
      pack r (s.flatMap vcode) b w := by
  have hm : memB (vcode l.1) (s.flatMap vcode) = true := (asg_codes s l.1).mpr h
  simp only [step, pack, item, remaining, seen, bits, output, unpairB_pairB, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, hm, bflag, sel, vcode_ne_nil]

theorem step_fresh (l : Literal) (r : Word) (s : List ℕ) (b : Bool) (bs w : Word)
    (h : l.1 ∉ s) :
    step (pack (encodeLiteral l ++ r) (s.flatMap vcode) (b :: bs) w) =
      pack r ((s ++ [l.1]).flatMap vcode) bs (w ++ if b then vcode l.1 else []) := by
  have hm : memB (vcode l.1) (s.flatMap vcode) = false := by
    cases hbit : memB (vcode l.1) (s.flatMap vcode)
    · rfl
    · exact False.elim (h ((asg_codes s l.1).mp hbit))
  simp only [step, pack, item, remaining, seen, bits, output, unpairB_pairB, headI_lit, dropI_lit]
  cases b <;> simp [encodeLiteral_eq, hm, bflag, sel, vcode_ne_nil, List.flatMap_append]

end PEqualNP.Outside.SatCodeSemantics
