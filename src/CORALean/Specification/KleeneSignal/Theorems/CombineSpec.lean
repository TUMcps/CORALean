module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineSpec
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# Point-wise combination of three-valued signals is point-wise

For valid inputs, each output of `combine(op,varargin)` is a valid signal whose value at every time
`t ≥ 0` is `op` applied to the Kleene values of the inputs at `t`: the Boolean and unknown parts
of an output are two outputs of the underlying Boolean combination.

## Inputs
* `T` – time type
* `ι` – index type of the inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on Kleene values
* `sig` – three-valued input signals
* `i` – output index

## Hypotheses
* `hv` – the input signals are valid

## Conclusion
* the output is valid and applies the operator at each time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.combine_spec {T : Type} [LinearOrder T] [Zero T] {ι κ : Type}
    [Fintype ι] [Nonempty ι] (op : (ι → Kleene) → κ → Kleene) (sig : ι → KleeneSignal T)
    (hv : ∀ k, (sig k).IsValid) (i : κ) : -- --- CONCL ---
    (KleeneSignal.combine op sig i).IsValid ∧ ∀ t : T, 0 ≤ t →
      (KleeneSignal.combine op sig i).at t = op (fun k => (sig k).at t) i := by -- --- PROOF ---
  unfold KleeneSignal.combine
  generalize hc : Sum.elim (fun k => (sig k).signal) (fun k => (sig k).isUnknown) = c
  generalize hk : (fun (args : ι ⊕ ι → Bool) (o : κ × Bool) =>
    if o.2 then (op (fun k => Kleene.ofBoolUnk (args (Sum.inl k)) (args (Sum.inr k))) o.1).isUnknown
    else (op (fun k => Kleene.ofBoolUnk (args (Sum.inl k)) (args (Sum.inr k))) o.1).toBool) = kOp
  -- the inputs of the Boolean combination are valid
  have hcv : ∀ x, (c x).IsValid := by
    rw [← hc]
    rintro (k | k)
    · exact (hv k).1
    · exact (hv k).2
  have hsp := fun o => PointSegmentSignal.combine_spec kOp c hcv o
  refine ⟨⟨(hsp (i, false)).1, (hsp (i, true)).1⟩, fun t ht => ?_⟩
  simp only [KleeneSignal.at]
  rw [(hsp (i, false)).2 t ht, (hsp (i, true)).2 t ht, ← hk, ← hc]
  simp only [Sum.elim_inl, Sum.elim_inr, Kleene.ofBoolUnk, if_true, Bool.false_eq_true, if_false]
  generalize op _ i = r
  cases r <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
