import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.CnfRestrictionMachine

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

/-! The clause-end transducer is adapted from upstream SatVerifierCPT. -/

private inductive IS : Type
  | b | t | f | e
  deriving DecidableEq

private instance : Fintype IS :=
  ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩

private def ieD : IS → Bool → IS × Option Bool
  | .b, false => (.f, none)
  | .f, false => (.t, none)
  | .t, _ => (.t, none)
  | _, _ => (.e, none)

private def ieF : IS → Option Bool
  | .t => some true
  | _ => none

private theorem ieD_e (l : List Bool) : fstRun ieD ieF IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

private theorem ieD_t (l : List Bool) : fstRun ieD ieF IS.t l = [true] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

private theorem ieD_run (s : List Bool) : fstRun ieD ieF IS.b s = bflag (isEnd s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [fstRun, ieD, ieD_e, ieD_t, isEnd, bflag]

theorem cpt_isEndF : CPT (fun s => bflag (isEnd s)) :=
  fst_polyTime _ _ _ ieD ieF IS.b (fun s => (ieD_run s).symm)

def assigned (z : Word) : Word := (unpairB z).1
def trueNames (z : Word) : Word := (unpairB (unpairB z).2).1
def rest (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def clause (z : Word) : Word := (unpairB (unpairB (unpairB (unpairB z).2).2).2).1
def satisfied (z : Word) : Word := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).1
def result (z : Word) : Word := (unpairB (unpairB (unpairB (unpairB (unpairB z).2).2).2).2).2

def pack (a b r c f out : Word) : Word :=
  pairB a (pairB b (pairB r (pairB c (pairB f out))))

def literalFlag (it yes : Word) : Word :=
  let p := bflag (polB it)
  sel (bflag (memB it.tail.tail yes)) (sel p [true] []) p

theorem literalFlag_spec (it yes : Word) :
    literalFlag it yes = bflag (memB it.tail.tail yes == polB it) := by
  unfold literalFlag
  cases memB it.tail.tail yes <;> cases polB it <;> rfl

def step (z : Word) : Word :=
  let a := assigned z
  let b := trueNames z
  let r := rest z
  let c := clause z
  let f := satisfied z
  let out := result z
  let it := headI r
  let tail := dropI r
  let keep := pack a b tail (c ++ it) f out
  let discard := pack a b tail c (sel (literalFlag it b) f [true]) out
  let close := pack a b tail [] [] (sel f (out ++ c ++ [false, false]) out)
  sel r z (sel (bflag (isEnd r)) (sel (bflag (memB it.tail.tail a)) keep discard) close)

theorem pack_cpt {a b r c f out : Word → Word}
    (ha : CPT a) (hb : CPT b) (hr : CPT r) (hc : CPT c) (hf : CPT f) (ho : CPT out) :
    CPT (fun z => pack (a z) (b z) (r z) (c z) (f z) (out z)) :=
  cpt_pairB2 ha (cpt_pairB2 hb (cpt_pairB2 hr (cpt_pairB2 hc (cpt_pairB2 hf ho))))

theorem step_cpt : CPT step := by
  have hA : CPT assigned := cpt_unpairB1
  have u₂ := cpt_unpairB2
  have hB : CPT trueNames := cpt_unpairB1_1 u₂
  have u₃ := cpt_unpairB2_1 u₂
  have hR : CPT rest := cpt_unpairB1_1 u₃
  have u₄ := cpt_unpairB2_1 u₃
  have hC : CPT clause := cpt_unpairB1_1 u₄
  have u₅ := cpt_unpairB2_1 u₄
  have hF : CPT satisfied := cpt_unpairB1_1 u₅
  have hO : CPT result := cpt_unpairB2_1 u₅
  have hItem := cpt_comp hR cpt_headI
  have hName := cpt_tail1 (cpt_tail1 hItem)
  have hTail := cpt_comp hR cpt_dropI
  have hP : CPT (fun z => bflag (polB (headI (rest z)))) :=
    cptl (cpt_comp (cpt_tail1 hItem) cpt_firstF) (fun z => by
      cases hh : headI (rest z) with
      | nil => rfl
      | cons a tail => cases tail <;> rfl)
  have hLit : CPT (fun z => literalFlag (headI (rest z)) (trueNames z)) :=
    cpt_sel (cpt_memB hName hB) (cpt_sel hP (cpt_const [true]) (cpt_const [])) hP
  have hKeep := pack_cpt hA hB hTail (cpt_app2 hC hItem) hF hO
  have hDrop := pack_cpt hA hB hTail hC (cpt_sel hLit hF (cpt_const [true])) hO
  have hClose := pack_cpt hA hB hTail (cpt_const []) (cpt_const [])
    (cpt_sel hF (cpt_app2 (cpt_app2 hO hC) (cpt_const [false, false])) hO)
  exact cptl (cpt_sel hR cpt_id (cpt_sel (cpt_comp hR cpt_isEndF)
    (cpt_sel (cpt_memB hName hA) hKeep hDrop) hClose)) (fun _ => rfl)

theorem pack_length (a b r c f out : Word) :
    (pack a b r c f out).length =
      2 * a.length + 2 * b.length + 2 * r.length + 2 * c.length + 2 * f.length + out.length + 5 := by
  simp only [pack, pairB_length]
  omega

theorem state_bound (z : Word) :
    2 * (assigned z).length + 2 * (trueNames z).length + 2 * (rest z).length +
      2 * (clause z).length + 2 * (satisfied z).length + (result z).length ≤ z.length := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have h3 := unpairB_length (unpairB (unpairB z).2).2
  have h4 := unpairB_length (unpairB (unpairB (unpairB z).2).2).2
  have h5 := unpairB_length (unpairB (unpairB (unpairB (unpairB z).2).2).2).2
  simp only [assigned, trueNames, rest, clause, satisfied, result]
  omega

theorem step_length (z : Word) : (step z).length ≤ z.length + 7 := by
  have hb := state_bound z
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  have hflag : (sel (literalFlag (headI (rest z)) (trueNames z)) (satisfied z) [true]).length ≤
      (satisfied z).length + 1 := by
    unfold sel
    split <;> simp
  have hout : (sel (satisfied z) (result z ++ clause z ++ [false, false]) (result z)).length ≤
      (result z).length + (clause z).length + 2 := by
    unfold sel
    split
    · simp [List.length_append]
      omega
    · omega
  have hdrop : (pack (assigned z) (trueNames z) (dropI (rest z)) (clause z)
    (sel (literalFlag (headI (rest z)) (trueNames z)) (satisfied z) [true]) (result z)).length ≤ z.length + 7 := by
    rw [pack_length]
    omega
  have hclose : (pack (assigned z) (trueNames z) (dropI (rest z)) [] []
    (sel (satisfied z) (result z ++ clause z ++ [false, false]) (result z))).length ≤ z.length + 7 := by
    simp only [pack_length, List.length_nil]
    omega
  simp only [step, sel]
  split
  · omega
  · split
    · split
      · simp only [pack_length, List.length_append]
        omega
      · simpa only [sel] using hdrop
    · simpa only [sel] using hclose

def run (p : Word × Word) : Word :=
  result (step^[p.1.length] (pack (unpairB p.2).1 (unpairB p.2).2 p.1 [] [] []))

theorem run_cpt : ComputableInPolyTime encodePair (fun x : Word => x) run := by
  obtain ⟨c⟩ := step_cpt
  have hLoop := Iter.iter_polyTime step c 7 step_length
  have f := cpt_comp cpt_pairB
    (pack_cpt (cpt_unpairB1_1 cpt_unpairB2) (cpt_unpairB2_1 cpt_unpairB2) cpt_unpairB1
      (cpt_const []) (cpt_const []) (cpt_const []))
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun p : Word × Word => pack (unpairB p.2).1 (unpairB p.2).2 p.1 [] [] []) :=
    cptl f (fun p => by simp [unpairB_pairB])
  have hOut : CPT result :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)))
  have h := cpt_comp (cpt_comp (cpt_pairG hs cpt_fst) hLoop) hOut
  exact h

end PEqualNP.Outside.CnfRestrictionMachine
