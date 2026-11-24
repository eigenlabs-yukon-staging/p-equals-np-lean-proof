import PEqualNP.Outside.ShortlexTruthTableSparseWitness

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

def scanChunks (emit advance : Word → Word) (fuel : Nat) (input : Word) : Word :=
  Nat.rec (fun _ => []) (fun _ scan rest =>
    if rest = [] then [] else emit rest ++ scan (advance rest)) fuel input

private def scanStep (emit advance : Word → Word) (s : Word) : Word :=
  let remaining := (unpairB s).2
  sel remaining s (pairB ((unpairB s).1 ++ emit remaining) (advance remaining))

private theorem scanStep_cpt {emit advance : Word → Word} (he : CPT emit) (ha : CPT advance) :
    CPT (scanStep emit advance) :=
  cpt_sel cpt_unpairB2 cpt_id (cpt_pairB2
    (cpt_app2 cpt_unpairB1 (cpt_comp cpt_unpairB2 he)) (cpt_comp cpt_unpairB2 ha))

private theorem scanStep_size {emit advance : Word → Word} (cap : Nat)
    (he : ∀ w, (emit w).length ≤ cap) (ha : ∀ w, (advance w).length ≤ w.length)
    (s : Word) : (scanStep emit advance s).length ≤ s.length + (2*cap+1) := by
  have hs := unpairB_length s
  have h₁ := he (unpairB s).2
  have h₂ := ha (unpairB s).2
  unfold scanStep
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length, List.length_append]
    omega

private theorem scanStep_invariant (emit advance : Word → Word) (n : Nat) (out rest : Word) :
    (unpairB ((scanStep emit advance)^[n] (pairB out rest))).1 =
      out ++ scanChunks emit advance n rest := by
  induction n generalizing out rest with
  | zero => simp [scanChunks,unpairB_pairB]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases empty : rest = []
    · subst rest
      change (unpairB ((scanStep emit advance)^[n]
        (scanStep emit advance (pairB out [])))).1 = _
      simp [scanStep,unpairB_pairB,sel,ih,scanChunks]
      cases n <;> rfl
    · have hs : scanStep emit advance (pairB out rest) =
          pairB (out ++ emit rest) (advance rest) := by
        simp [scanStep,unpairB_pairB,sel,empty]
      rw [hs,ih]
      simp [scanChunks,empty,List.append_assoc]

/-- A scan may append a bounded chunk and advance to a residual input no longer
than the old one. Running for the original input length has a measured machine. -/
theorem scanChunks_polyTime (emit advance : Word → Word) (he : CPT emit) (ha : CPT advance)
    (cap : Nat) (size : ∀ w, (emit w).length ≤ cap)
    (remaining : ∀ w, (advance w).length ≤ w.length) :
    CPT (fun w => scanChunks emit advance w.length w) := by
  have h :=
    cpt_unpairB1_1 (cpt_iterGrow (scanStep_cpt he ha) (2*cap+1)
      (scanStep_size cap size remaining) cpt_id (cpt_pairB2 (cpt_const []) cpt_id))
  refine bf_cptl h (fun w => ?_)
  rw [scanStep_invariant]
  simp

private def quoteBits (w : Word) : Word := w.flatMap (fun b => [true,b])

private theorem quoteBits_length (w : Word) : (quoteBits w).length = 2*w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp [quoteBits] at ih ⊢
    omega

private theorem quoteBits_lt (a b u v : Word) (h : a < b) :
    quoteBits a ++ false::u < quoteBits b ++ false::v := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      change false::u < true::b::(quoteBits bs ++ false::v)
      exact List.cons_lt_cons_iff.mpr (Or.inl (by decide))
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      change true::a::(quoteBits as ++ false::u) < true::b::(quoteBits bs ++ false::v)
      apply List.cons_lt_cons_iff.mpr
      refine Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr ?_⟩
      rcases List.cons_lt_cons_iff.mp h with lt | ⟨eq,rest⟩
      · exact Or.inl lt
      · exact Or.inr ⟨eq, ih bs rest⟩

private theorem headWord_cpt : CPT (fun w => [w.headD false]) := by
  refine bf_cptl (cpt_sel (cpt_bitFlag wordHead_polyTime) (cpt_const [false]) (cpt_const [true])) ?_
  intro w
  cases w.headD false <;> rfl

private theorem quoteScan (n : Nat) (w : Word) (h : w.length ≤ n) :
    scanChunks (fun w => [true,w.headD false]) List.tail n w = quoteBits w := by
  induction n generalizing w with
  | zero =>
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    rfl
  | succ n ih =>
    cases w with
    | nil => rfl
    | cons b w =>
      change [true,b] ++ scanChunks (fun w => [true,w.headD false]) List.tail n w = _
      rw [ih w (by simpa using h)]
      rfl

private theorem quoteBits_cpt : CPT quoteBits :=
  bf_cptl (scanChunks_polyTime _ _ (cpt_cons1 true headWord_cpt) cpt_tail 2 (by simp) (by simp))
    (fun w => quoteScan w.length w le_rfl)

private def scanEmit (w : Word) : Word :=
  if w.headD false then [w.tail.headD false] else []

private def scanAdvance (w : Word) : Word :=
  if w.headD false then w.tail.tail else []

private theorem scanEmit_cpt : CPT scanEmit := by
  refine bf_cptl (cpt_sel (cpt_bitFlag wordHead_polyTime) (cpt_const [])
    (cpt_comp cpt_tail headWord_cpt)) ?_
  intro w
  cases w with
  | nil => rfl
  | cons b w => cases b <;> simp [scanEmit,bflag,sel]

private theorem scanAdvance_cpt : CPT scanAdvance := by
  refine bf_cptl (cpt_sel (cpt_bitFlag wordHead_polyTime) (cpt_const [])
    (cpt_comp (f := List.tail) (g := List.tail) cpt_tail cpt_tail)) ?_
  intro w
  cases w with
  | nil => rfl
  | cons b w => cases b <;> simp [scanAdvance,bflag,sel]

private theorem scanEmpty (n : Nat) : scanChunks scanEmit scanAdvance n [] = [] := by
  cases n <;> rfl

private theorem decodeScan (n : Nat) (w suffix : Word) (h : w.length + 1 ≤ n) :
    scanChunks scanEmit scanAdvance n (quoteBits w ++ false::suffix) = w := by
  induction w generalizing n with
  | nil =>
    cases n with
    | zero => simp at h
    | succ n =>
      change scanChunks scanEmit scanAdvance n [] = []
      exact scanEmpty n
  | cons b w ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      change b :: scanChunks scanEmit scanAdvance n (quoteBits w ++ false::suffix) = b :: w
      rw [ih n (by simp at h; omega)]

def decodeLexPad (z : Word) : Word := scanChunks scanEmit scanAdvance z.length z

theorem decodeLexPad_cpt : CPT decodeLexPad :=
  scanChunks_polyTime _ _ scanEmit_cpt scanAdvance_cpt 1
    (fun w => by unfold scanEmit; split <;> simp)
    (fun w => by unfold scanAdvance; split <;> simp <;> omega)

def padLex (n : Nat) (w : Word) : Word :=
  quoteBits w ++ false :: un (2*(n-w.length))

theorem padLex_length (n : Nat) (w : Word) (h : w.length ≤ n) :
    (padLex n w).length = 2*n+1 := by
  simp [padLex,quoteBits_length]
  omega

theorem padLex_order (n : Nat) (u w : Word) (h : u < w) :
    padLex n u < padLex n w := quoteBits_lt _ _ _ _ h

theorem decodeLexPad_padLex (n : Nat) (w : Word) : decodeLexPad (padLex n w) = w := by
  apply decodeScan
  simp [padLex,quoteBits_length]
  omega

theorem padLex_cpt (p : Polynomial Nat) :
    ComputableInPolyTime encodePair (fun x => x)
      (fun q : Word × Word => padLex (p.eval q.1.length) q.2) := by
  have hquote := cpt_comp cpt_unpairB2 quoteBits_cpt
  have hs := cpt_unpairB2_1 (cpt_comp cpt_unpairB (padShortlex_cpt p))
  have h := cpt_app2 hquote (cpt_cons1 false hs)
  refine cpt_fromRaw (f := fun q => padLex (p.eval q.1.length) q.2) (bf_cptl h ?_)
  intro x
  simp [padLex,padShortlex,unpairB_pairB]

private def decodeTaggedLex (s : Word) : Word := sel s [] (true :: decodeLexPad s.tail)

private theorem decodeTaggedLex_cpt : CPT decodeTaggedLex :=
  cpt_sel cpt_id (cpt_const []) (cpt_cons1 true (cpt_comp cpt_tail decodeLexPad_cpt))

/-- Under the bounded sparse reduction hypothesis, recover the least verifier
witness in ordinary lexicographic order even when valid lengths differ. -/
theorem LexTruthTableSparseWitness (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ∃ f : Word → Word, CPT f ∧ ∀ x : Word,
      (f x = [] ∧ ∀ w : Word, (x,w) ∉ R) ∨
        ∃ w : Word, f x = true :: w ∧ (x,w) ∈ R ∧
          ∀ u : Word, (x,u) ∈ R → w ≤ u := by
  obtain ⟨E,hE,hSpec⟩ := measuredCanonicalPadding R hR
    (fun q => padLex (p.eval q.1.length) q.2) (padLex_cpt p) decodeLexPad decodeLexPad_cpt
    (fun x w => decodeLexPad_padLex (p.eval x.length) w)
  have hLen (x z : Word) (hz : (x,z) ∈ E) :
      z.length = (Polynomial.C 2*p+1).eval x.length := by
    obtain ⟨w,hw,rfl⟩ := (hSpec x z).mp hz
    simpa using padLex_length (p.eval x.length) w (bound x w hw)
  obtain ⟨run,hr,hs⟩ := VariableTruthTableSparseWitness E hE (Polynomial.C 2*p+1)
    hLen A B hA s sparse k q hq T hT relation
  refine ⟨fun x => decodeTaggedLex (run x),cpt_comp hr decodeTaggedLex_cpt,fun x => ?_⟩
  rcases hs x with ⟨hn,hNo⟩ | ⟨z,hz,ha,hMin⟩
  · refine Or.inl ⟨by simp [hn,decodeTaggedLex],fun w hw => ?_⟩
    exact hNo _ ((hSpec _ _).mpr ⟨w,hw,rfl⟩)
  · obtain ⟨w,hw,rfl⟩ := (hSpec _ _).mp ha
    refine Or.inr ⟨w,by simp [hz,decodeTaggedLex,sel,decodeLexPad_padLex],hw,fun u hu => ?_⟩
    apply le_of_not_gt
    intro h
    have hc := (hSpec x (padLex (p.eval x.length) u)).mpr ⟨u,hu,rfl⟩
    exact not_lt_of_ge (hMin _ hc) (padLex_order (p.eval x.length) u w h)

end PEqualNP.Outside
