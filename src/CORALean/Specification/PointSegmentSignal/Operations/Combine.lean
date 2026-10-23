module

public import CORALean.Specification.PointSegmentSignal.Operations.CombineLoop

@[expose] public section

/-!
# Point-wise combination of signals

`combine(op,varargin)` of `pointSegmentSignal.m`: the signals `sig k` combined point-wise by `op`,
which maps the values at a point to `o` output values; output `i` is a signal of its own. Each
output runs the loop on its own, as CORA's outputs share only the traversal of the input times.

## Inputs
* `T` – time type
* `ι` – index type of the inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on Boolean values
* `sig` – input signals

## Output
* the combined signals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs = combine(op,varargin)`. -/
def PointSegmentSignal.combine {T : Type} [TimeOrder T] [Zero T] {ι κ : Type} [FinEnum ι]
    (op : (ι → Bool) → κ → Bool) (sig : ι → PointSegmentSignal T) :
    κ → PointSegmentSignal T := fun i =>
  -- 1. inIdx = ones(1,numInputs)
  let inIdx : ι → ℕ := fun _ => 1
  -- 2. loop, once per time point of the inputs
  let fuel := ∑ k, (sig k).length + 1
  let r := PointSegmentSignal.combineLoop (fun a => op a i) sig fuel inIdx [] []
  ⟨r.1, r.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
