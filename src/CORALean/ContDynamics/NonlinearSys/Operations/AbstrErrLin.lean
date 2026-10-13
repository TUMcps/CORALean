import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul

/-!
# The linearization error of a second-order expansion

CORA's `priv_abstrerr_lin` at `tensorOrder = 2`, [1, Prop. 3.7] = [2, Prop. 1]: the box
`[-l, l]` with `lᵢ = ½ γᵀ Hᵢ γ`, where `γ` bounds `|z - z✱|` over the set the step
runs on and `Hᵢ` bounds the second derivative of coordinate `i` entrywise.

`γ` is the proposition's `|c - z✱| + Σⱼ |g⁽ʲ⁾|`, read off a zonotope rather than
off a box, which is what lets `abstrErrLin_center_subset` name its centre.

`H` is data, as `precompStatError`'s `Q` is: nothing here differentiates `f`, and
a wrong `H` yields a box `AbstractionError.of_hessian` cannot certify rather than
an unsound one. Real only: `NonlinearSys` carries no scalar and the certificate
slot is generic, so a float run fills it with its own box rather than this one.

The state and the input are stacked into one `Vec ℝ d`, CORA's `dz = [dx; du]`,
so `Hᵢ` is a single square matrix per coordinate whose off-diagonal blocks are
the mixed derivatives. `d` is free here and `n + m` at the use site.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
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
