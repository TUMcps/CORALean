module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Cube
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# `girardReach`: [1, Alg. 1]

Approximating the reachable set of `x' = Ax + u`, `‖u‖ ≤ µ`, from a zonotope `I` over
`[0, T]` at step `r`: the first time interval `Q₀ = P₀ + □(α_r + β_r)` by [1, Lemma 2], then
`Qᵢ = e^{rA}Qᵢ₋₁ + □(β_r)` by [1, Lemma 1], the union `R` of all of them returned as the list
of the `Qᵢ`. One `let` per printed line.

Where the listing is read with care:

* it returns `R_N`, but its loop stops at `R_{N-1}` and [1, Thm. 1] is about `R_{N-1}`; this
  returns `R_{N-1}`, the `N` sets `Q₀, ..., Q_{N-1}` covering `[0, N r]`;
* `N = T/r` is assumed an integer; here `N = ⌈T/r⌉`, which covers `[0, T]` either way and is
  `T/r` when that is an integer;
* `sup_{x∈I} ‖x‖` is computed, as the largest `Zonotope.absBound`: a coordinate's reach
  `|cⱼ| + Σᵢ|gᵢⱼ|` is attained, so their maximum is the supremum of the infinity norm;
* `β_r` divides by `‖A‖`, which the theorems take positive.

Taken at the exact `e^{rA}` and `e^{r‖A‖}`; it runs in floats as `girardReachFloat`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: `Q₀ = P₀ + □(α_r + β_r)`, then `Qᵢ = e^{rA}Qᵢ₋₁ + □(β_r)` for `i < N`,
returning `R_{N-1} = Q₀ ∪ ... ∪ Q_{N-1}` as the list of its members. -/
noncomputable def LinearSys.girardReach (sys : LinearSys 𝕋 n) (I : Zonotope (Vec ℝ n))
    (μ r T : ℝ) : List (Zonotope (Vec ℝ n)) :=
  let A := toRealMat sys.A
  -- 1. N = ⌈T/r⌉
  let N := ⌈T / r⌉₊
  -- 2. α_r = (e^{r‖A‖} - 1 - r‖A‖) sup_{x∈I} ‖x‖
  let αr := (Real.exp (r * ‖A‖) - 1 - r * ‖A‖) * Finset.univ.fold max 0 I.absBound
  -- 3. β_r = (e^{r‖A‖} - 1)/‖A‖ · μ
  let βr := (Real.exp (r * ‖A‖) - 1) / ‖A‖ * μ
  -- 4. P₀, the convex hull of I and e^{rA}I
  let P₀ := I.linComb (I.mtimes (exp (r • A)))
  -- 5. Q₀ = P₀ + □(α_r + β_r)
  let Q₀ := P₀.plus (Zonotope.cube n (αr + βr))
  -- 6. R₀ = Q₀
  let R₀ := [Q₀]
  -- 7. for i = 1 … N - 1
  ((List.range (N - 1)).foldl
    (fun (QR : Zonotope (Vec ℝ n) × List (Zonotope (Vec ℝ n))) _ =>
      -- 8. Pᵢ = e^{rA} Qᵢ₋₁
      let Pᵢ := QR.1.mtimes (exp (r • A))
      -- 9. Qᵢ = Pᵢ + □(β_r)
      let Qᵢ := Pᵢ.plus (Zonotope.cube n βr)
      -- 10. Rᵢ = Rᵢ₋₁ ∪ Qᵢ
      let Rᵢ := QR.2 ++ [Qᵢ]
      (Qᵢ, Rᵢ))
    (Q₀, R₀)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
