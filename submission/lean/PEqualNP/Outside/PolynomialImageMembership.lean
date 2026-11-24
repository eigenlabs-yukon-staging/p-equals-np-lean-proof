import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Word" => List Bool

private def words : List Word → Word := List.foldr pairB []

private theorem words_length (xs : List Word) : xs.length ≤ (words xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change xs.length + 1 ≤ (pairB x (words xs)).length
    rw [pairB_length]
    omega

private def query (f : Word × Word → Word) (s : Word) : Word :=
  let pivot := (unpairB s).1
  let rest := (unpairB s).2
  let key := (unpairB rest).1
  let R := (unpairB rest).2
  let tail := (unpairB R).1
  let flags := (unpairB R).2
  let eq := bflag (decide (f (pivot, (unpairB tail).1) = key))
  let next := pairB pivot (pairB key (pairB (unpairB tail).2 (flags ++ eq)))
  sel tail s next

private theorem query_length (f : Word × Word → Word) (s : Word) :
    (query f s).length ≤ s.length + 4 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have h₃ := unpairB_length (unpairB (unpairB s).2).2
  have h₄ := unpairB_length (unpairB (unpairB (unpairB s).2).2).1
  unfold query
  dsimp only
  apply sel_length
  · omega
  · rw [pairB_length, pairB_length, pairB_length, List.length_append]
    have he := bf_bflag_length (decide
      (f ((unpairB s).1, (unpairB (unpairB (unpairB (unpairB s).2).2).1).1) =
        (unpairB (unpairB s).2).1))
    omega

private theorem query_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    CPT (query f) := by
  have hp := cpt_unpairB1
  have hR := cpt_unpairB2
  have hk := cpt_unpairB1_1 hR
  have hT := cpt_unpairB2_1 hR
  have ht := cpt_unpairB1_1 hT
  have hfl := cpt_unpairB2_1 hT
  have hhead := cpt_unpairB1_1 ht
  have htail := cpt_unpairB2_1 ht
  have him := cpt_comp (cpt_pair hp hhead) hf
  have heq := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF him hk
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hp (cpt_pairB2 hk (cpt_pairB2 htail
    (cpt_app2 hfl heq))))) (fun _ => rfl)

private theorem query_nil (f : Word × Word → Word) (p k fl : Word) :
    query f (pairB p (pairB k (pairB [] fl))) = pairB p (pairB k (pairB [] fl)) := by
  simp [query, unpairB_pairB]

private theorem query_cons (f : Word × Word → Word) (p k x : Word) (xs : List Word) (fl : Word) :
    query f (pairB p (pairB k (pairB (words (x :: xs)) fl))) =
    pairB p (pairB k (pairB (words xs) (fl ++ bflag (decide (f (p,x) = k))))) := by
  have hn : pairB x (words xs) ≠ [] := by
    intro h
    have e := congrArg List.length h
    rw [pairB_length] at e
    simp at e
  change pairB x (List.foldr pairB [] xs) ≠ [] at hn
  simp [query, words, unpairB_pairB, sel, hn]

private theorem query_iter (f : Word × Word → Word) (p k : Word)
    (xs : List Word) (n : Nat) (hn : xs.length ≤ n) (fl : Word) :
    ∃ fin : Word, (query f)^[n] (pairB p (pairB k (pairB (words xs) fl))) =
      pairB p (pairB k (pairB [] fin)) ∧
      (fin = [] ↔ fl = [] ∧ ∀ x ∈ xs, f (p,x) ≠ k) := by
  induction xs generalizing n fl with
  | nil =>
    exact ⟨fl, Function.iterate_fixed (query_nil f p k fl) n, by simp⟩
  | cons x xs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply, query_cons]
      obtain ⟨fin, hstate, hfin⟩ := ih n (by simpa using hn) (fl ++ bflag (decide (f (p,x) = k)))
      exact ⟨fin, hstate, by
        rw [hfin, List.append_eq_nil_iff, bflag_eq_nil]
        simp [and_assoc]⟩

private def pack (p k : Word) (xs : List Word) : Word :=
  pairB p (pairB k (words xs))

private def start (s : Word) : Word :=
  pairB (unpairB s).1 (pairB (unpairB (unpairB s).2).1 (pairB (unpairB (unpairB s).2).2 []))

def imageLookup (f : Word × Word → Word) (s : Word) : Bool :=
  let z := (unpairB (unpairB ((query f)^[s.length] (start s))).2).2
  !(unpairB z).2.isEmpty

theorem imageLookup_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool (imageLookup f) := by
  have hstart : CPT start :=
    bf_cptl (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB2)
      (cpt_pairB2 (cpt_unpairB2_1 cpt_unpairB2) (cpt_const [])))) (fun _ => rfl)
  have hrun := cpt_iterGrow (query_polyTime hf) 4 (query_length f) cpt_id hstart
  exact bf_cptl (cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hrun))) bf_cpt_neL)
    (fun _ => rfl)

theorem imageLookup_spec (f : Word × Word → Word) (p k : Word) (xs : List Word) :
    imageLookup f (pairB p (pairB k (xs.foldr pairB []))) = true ↔
      ∃ x ∈ xs, f (p,x) = k := by
  change imageLookup f (pack p k xs) = true ↔ _
  have hn : xs.length ≤ (pack p k xs).length := by
    unfold pack
    rw [pairB_length, pairB_length]
    have h := words_length xs
    omega
  obtain ⟨fl, hs, hfl⟩ := query_iter f p k xs (pack p k xs).length hn []
  have he : start (pack p k xs) = pairB p (pairB k (pairB (words xs) [])) := by
    simp [start, pack, unpairB_pairB]
  simp [imageLookup, he, hs, unpairB_pairB, hfl]

/-- An exact polynomial-time lookup of a reduction image among a variable-size encoded
list. The explicit encoding in the statement uses unary length-delimited words. -/
theorem PolynomialImageMembership (f : Word × Word → Word)
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    ∃ matchImage : Word → Bool,
      ComputableInPolyTime (fun x => x) Computability.encodeBool matchImage ∧
        ∀ (p k : Word) (xs : List Word),
          let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
          matchImage (consWord p (consWord k (xs.foldr consWord []))) = true ↔
            ∃ x ∈ xs, f (p,x) = k := by
  exact ⟨imageLookup f, imageLookup_polyTime hf, imageLookup_spec f⟩

end PEqualNP.Outside
