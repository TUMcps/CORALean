import CORALean.ContDynamics.LinearSysDT.Operations.IntervalObserverCoord

/-!
# The interval observer based on a coordinate transformation

[1, Thm. 5], its Eqs. 42e-42f: the bounds `x̲ᵗ_k = (S⁻¹)⁺ z̲_k - (S⁻¹)⁻ z̅_k`,
`x̅ᵗ_k = (S⁻¹)⁺ z̅_k - (S⁻¹)⁻ z̲_k` for `k ≥ 1`, from the transformed observer
`intervalObserverCoord`, and the given `x̲ᵗ₀`, `x̅ᵗ₀` at `k = 0`.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.intervalObserverTransformed (A : Mat ℝ n n) (B : Mat ℝ n nu)
    (C : Mat ℝ ny n) (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (S : Mat ℝ n n)
    (wl wu : Vec ℝ nw) (vl vu : Vec ℝ nv) (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ nu)
    (y : ℕ → Vec ℝ ny) : ℕ → Interval (Vec ℝ n)
  | 0 => ⟨xl₀, xu₀⟩
  | k + 1 =>
    let Z := LinearSysDT.intervalObserverCoord A B C E F L S wl wu vl vu xl₀ xu₀ u y (k + 1)
    let Tp := S⁻¹.map (max 0)  -- `(S⁻¹)⁺`
    let Tn := Tp - S⁻¹  -- `(S⁻¹)⁻`
    ⟨Tp *ᵥ Z.inf - Tn *ᵥ Z.sup, Tp *ᵥ Z.sup - Tn *ᵥ Z.inf⟩  -- (42f), (42e)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
