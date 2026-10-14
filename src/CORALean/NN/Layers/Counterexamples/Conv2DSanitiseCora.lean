module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Layer.conv2DSanitiseCora`: the repair of inverted center bounds in `nnConv2DLayer`

`nn/layers/linear/nnConv2DLayer.m`, `evaluateZonotopeBatch`, l. 182-185 (with
`options.nn.interval_center`, the interval center of `c(:,1,:)` and `c(:,2,:)`):

```
if any(cl > cu, 'all')
    t = cl;
    cl = min(t, cu);
    cu = max(t, t);
end
```

The comment says it sanitizes bounds "to prevent interval constructor crash". For an entry with
`cl > cu` this swaps them. For every other entry `cu` becomes `max(t,t) = t`, the old `cl`: the
interval `[cl, cu]` collapses to the point `cl`. `max(t, cu)` is what was meant. The batch is
repaired as a whole as soon as one entry is inverted (`any`). `neuralNetwork/evaluateZonotopeBatch`
is public, and `verify` sets `interval_center` (l. 97, 578, 589) and propagates through
`evaluateZonotopeBatch_`. One entry per neuron and batch element, given as functions of the entry
index. Read from the source, not run.

# CORA's center repair collapses the entries that were fine

Two batch elements with `cl = (0, 2)`, `cu = (1, 1)`: the second is inverted, so the repair runs,
turns it into `[1, 2]` and the first `[0, 1]` into `[0, 0]`: the layer is then applied to the
point `0`, and the value `1`, which the first element can take, is lost. Read from the source,
not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
open scoped Classical in
/-- The bounds `(cl, cu)` after the repair, entry by entry. -/
noncomputable def Layer.conv2DSanitiseCora {ι : Type} (cl cu : ι → ℝ) : (ι → ℝ) × (ι → ℝ) :=
  -- any(cl > cu, 'all')
  if ∃ i, cu i < cl i then
    -- cl = min(t, cu);  cu = max(t, t)
    (fun i => min (cl i) (cu i), fun i => max (cl i) (cl i))
  else (cl, cu)

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `cl = (0, 2)`, `cu = (1, 1)` the first entry `[0, 1]` becomes `[0, 0]`, which does not
contain `1`. -/
theorem Layer.conv2DSanitise_cora_counterexample :
    (![0, 2] : Fin 2 → ℝ) 0 ≤ 1 ∧ (1 : ℝ) ≤ (![1, 1] : Fin 2 → ℝ) 0 ∧
      (Layer.conv2DSanitiseCora (![0, 2] : Fin 2 → ℝ) ![1, 1]).2 0 <
        1 := by
  have h : ∃ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i < (![0, 2] : Fin 2 → ℝ) i := ⟨1, by simp⟩
  refine ⟨by simp, by simp, ?_⟩
  simp [Layer.conv2DSanitiseCora, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
