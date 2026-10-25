module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The linearization error of a second-order expansion

CORA's `priv_abstrerr_lin` at `tensorOrder = 2`, [1, Prop. 1]: the box `[-l, l]` with
`lᵢ = ½ γᵀ Hᵢ γ`, where `γ` bounds `|z - z✱|` over the set the step runs on and `Hᵢ` bounds the
second derivative of coordinate `i` entrywise. `γ` is the proposition's `|c - z✱| + Σⱼ |g⁽ʲ⁾|`,
read off a zonotope rather than off a box, which is what lets `abstrErrLin_center_subset` name its
center. `H` is data, as `precompStatError`'s `Q` is: nothing here differentiates `f`, and a wrong
`H` yields a box `IsAbstractionError.of_hessian` cannot certify rather than an unsound one. Real
only. The state and the input are stacked into one `Vec ℝ d`, CORA's `dz = [dx; du]`, so `Hᵢ` is
a single square matrix per coordinate; `d` is `n + m` at the use site.

## Inputs
* `H` – second-derivative bounds
* `Z` – region of the remainder
* `zs` – expansion point

## Output
* the symmetric box bounding the second-order remainder

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". 2008 47th IEEE Conference on Decision
      and Control, 2008.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {d n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The symmetric box `[-l, l]` bounding a second-order remainder over `Z`, at
the expansion point `zs` and the entrywise second-derivative bound `H`. -/
noncomputable def abstrErrLin (H : Fin n → Mat ℝ d d) (Z : Real.Zonotope (Vec ℝ d)) (zs : Vec ℝ d) :
    Real.Interval (Vec ℝ n) :=
  let γ : Vec ℝ d := fun j => |Z.c j - zs j| + ∑ k, |Z.G k j|
  let l : Vec ℝ n := fun i => γ ⬝ᵥ (H i *ᵥ γ) / 2
  ⟨-l, l⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
