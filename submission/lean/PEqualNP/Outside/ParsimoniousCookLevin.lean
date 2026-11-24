import PEqualNP.Outside.CompileValidInput
import PEqualNP.Outside.MeasuredParsimoniousTableau
import PEqualNP.Library.SearchHelpers.TableauAssembly
import PEqualNP.Outside.TableauWidth

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Search

theorem PEqualNP.Outside.ParsimoniousCookLevin :
    ∀ (v : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      ComputableInPolyTime encodePair Computability.encodeBool v →
      ∃ F : List Bool → CNF,
        ComputableInPolyTime (fun x : List Bool => x) (fun y : List Bool => y)
          (fun x => encodeCNF (F x)) ∧
        ∀ x : List Bool,
          let φ := F x
          IsKCNF 4 φ ∧
          Nonempty ({w : List Bool // w.length ≤ p.eval x.length ∧ v (x,w) = true} ≃
                    {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
                      CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                        then a ⟨i,h⟩ else false) φ = true}) := by
  intro v p hv
  obtain ⟨machine⟩ := hv
  obtain ⟨c,d,hkin,hcompile⟩ := compile_valid machine.tm machine.inputAlphabet machine.outputAlphabet
  have run (x w : List Bool) :
      ∃ n, n ≤ machine.time.eval (x.length + w.length) ∧
        c.outputsWithin ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2)
          (d * n + d) [bitCode (v (x,w))] := by
    have out := machine.outputsFun (x,w)
    have h := hcompile (encodePair (x,w)) (v (x,w)) out.steps out.evals_in_steps
    rw [PEqualNP.Library.SearchHelpers.Tab.Edge.map_symIn_encodePair] at h
    exact ⟨out.steps, by simpa [encodePair] using out.steps_le_m, h⟩
  let q : Polynomial ℕ := Polynomial.C d * machine.time.comp (Polynomial.X + p) + Polynomial.C d
  have eval_q (n : ℕ) : q.eval n = d * machine.time.eval (n + p.eval n) + d := by
    simp [q, Polynomial.eval_comp]
  refine ⟨PEqualNP.Outside.OneHot.words c p q,
    PEqualNP.Outside.OneHot.words_cnfC c p q, ?_⟩
  intro x
  refine ⟨PEqualNP.Outside.OneHot.formula_width c _ _ _, ?_⟩
  have hzs : ∀ z ∈ x.map (fun b => cond b 1 0), z < 4 := by
    intro z hz
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
    cases b <;> decide
  let equiv := PEqualNP.Outside.OneHot.models_equiv c _ (p.eval x.length) (q.eval x.length) hzs hkin
  refine ⟨(Equiv.subtypeEquivRight ?_).trans equiv⟩
  intro w
  refine and_congr_right fun hw => ?_
  let input := (x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2
  change v (x,w) = true ↔ c.outputsWithin input (q.eval x.length) [1]
  obtain ⟨n,hn,ho⟩ := run x w
  have hn' := hn.trans (PEqualNP.Library.Machines.eval_mono machine.time
    (Nat.add_le_add_left hw x.length))
  have hN : d * n + d ≤ q.eval x.length := by
    rw [eval_q]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hn') d
  have hout := Code.outputsWithin_mono c input hN _ ho
  constructor
  · intro h
    simpa [h,bitCode] using hout
  · intro h
    have heq := h.2.symm.trans hout.2
    cases hv' : v (x,w) with
    | true => rfl
    | false => simp [hv',bitCode] at heq
