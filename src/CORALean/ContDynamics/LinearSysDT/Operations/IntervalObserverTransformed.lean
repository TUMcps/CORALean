module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverCoord

@[expose] public section

/-!
# The interval observer based on a coordinate transformation

[1, Thm. 5], its Eqs. 42e-42f: the bounds `x̲ᵗ_k = (S⁻¹)⁺ z̲_k - (S⁻¹)⁻ z̅_k`,
`x̅ᵗ_k = (S⁻¹)⁺ z̅_k - (S⁻¹)⁻ z̲_k` for `k ≥ 1`, from the transformed observer
`intervalObserverCoord`, and the given `x̲ᵗ₀`, `x̅ᵗ₀` at `k = 0`.

## Inputs
* `sys` – system
* `L` – observer gain
* `S` – coordinate transformation
* `wl` – lower disturbance bound
* `wu` – upper disturbance bound
* `vl` – lower noise bound
* `vu` – upper noise bound
* `xl₀` – lower initial bound
* `xu₀` – upper initial bound
* `u` – inputs
* `y` – measurements

## Output
* the state interval mapped back from transformed coordinates

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.intervalObserverTransformed (sys : LinearSysDT ℝ n)
    (L : Mat ℝ n sys.q) (S : Mat ℝ n n)
    (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s) (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) : ℕ → Interval (Vec ℝ n)
  | 0 => ⟨xl₀, xu₀⟩
  | k + 1 =>
    let Z := LinearSysDT.intervalObserverCoord sys L S wl wu vl vu xl₀ xu₀ u y (k + 1)
    let Tp := S⁻¹.map (max 0)  -- `(S⁻¹)⁺`
    let Tn := Tp - S⁻¹  -- `(S⁻¹)⁻`
    ⟨Tp *ᵥ Z.inf - Tn *ᵥ Z.sup, Tp *ᵥ Z.sup - Tn *ᵥ Z.inf⟩  -- (42f), (42e)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
