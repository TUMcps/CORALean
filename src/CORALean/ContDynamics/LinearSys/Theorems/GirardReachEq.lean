module

public import CORALean.ContDynamics.LinearSys.Operations.GirardReach

@[expose] public section

/-!
# What `girardReach` returns, in closed form

[1, Alg. 1]'s loop unrolled: the list is `Q₀, f(Q₀), ..., f^{N-1}(Q₀)`, `f(Q) = e^{rA}Q + □(β_r)`
being the loop body and `N = ⌈T/r⌉` (at least one set, `Q₀`, even at `T ≤ 0`). What the
theorems about `girardReach` reason about is this iterate, not the fold.

## Inputs
* `sys` – linear system
* `I` – initial zonotope
* `μ` – input norm bound
* `r` – step length
* `T` – time horizon

## Hypotheses
* none

## Conclusion
* the list is the first enclosure iterated by the step map

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` passes of a loop that maps its state and appends the result. -/
private theorem aux_foldl_iterate {α : Type} (f : α → α) (a : α) (k : ℕ) : -- --- CONCL ---
    (List.range k).foldl (fun (QR : α × List α) (_ : ℕ) => (f QR.1, QR.2 ++ [f QR.1])) (a, [a])
      = (f^[k] a, (List.range (k + 1)).map fun i => f^[i] a) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.range_succ, Function.iterate_succ_apply']


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1], unrolled: `R_{N-1}` is `Q₀, f(Q₀), ..., f^{N-1}(Q₀)`. -/
theorem LinearSys.girardReach_eq (sys : LinearSys 𝕋 n) (I : Zonotope (Vec ℝ n))
    (μ r T : ℝ) : -- --- CONCL ---
    sys.girardReach I μ r T
      = (List.range (⌈T / r⌉₊ - 1 + 1)).map fun i =>
          (fun Q : Zonotope (Vec ℝ n) => (Q.mtimes (exp (r • toRealMat sys.A))).plus
            (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
              * μ)))^[i]
          ((I.linComb (I.mtimes (exp (r • toRealMat sys.A)))).plus
            (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖)
              * Finset.univ.fold max 0 I.absBound
              + (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
                * μ))) := by -- --- PROOF ---
  simp only [LinearSys.girardReach]
  exact congrArg Prod.snd (aux_foldl_iterate (fun Q : Zonotope (Vec ℝ n) =>
    (Q.mtimes (exp (r • toRealMat sys.A))).plus
      (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ))) _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
