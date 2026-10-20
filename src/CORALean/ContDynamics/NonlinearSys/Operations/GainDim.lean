module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrSolInf
public import CORALean.Global.BoxDiameter

@[expose] public section

/-!
# The gain of one dimension

`[1, Def. 5]`: `φᵢ(h;δ) = dᵢ(box(R^∞_abs(δh))) / dᵢ(box(R^∞_abs(h)))`, how much of dimension `i`
of the local abstraction error survives shrinking the span from `h` to `δh`. `[1, Thm. 2]` is its
limit as `h → 0`, and `[1, Prop. 1]` is what lets both be computed from `Ψ(h)`'s generators
rather than from the set. **Where the denominator vanishes** Lean's `x / 0 = 0` makes `φᵢ` zero,
and that is not what `[1, Def. 5]` means. By `[1, Def. 6]` the denominator vanishes identically in
`h` exactly when dimension `i` has gain order `∞`. The nonvanishing hypothesis belongs to whatever
reads `φᵢ`, as in `[1, (19)]`, which quantifies over the dimensions with `Ψᵢ > 0`, and not to the
definition, which has to be total.

## Inputs
* `A` – matrix as a function of the step
* `Ψ` – error set as a function of the step
* `h` – step size
* `δ` – shrink factor
* `i` – dimension

## Output
* the share of its width dimension `i` keeps

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φᵢ(h;δ)`: the width dimension `i` of the error set keeps when the time span
shrinks from `h` to `δh`. -/
noncomputable def gainDim (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (h δ : ℝ)
    (i : Fin n) : ℝ :=
  boxDiameter (abstrSolInf A Ψ (δ * h)) i / boxDiameter (abstrSolInf A Ψ h) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
