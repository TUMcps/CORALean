import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.Global.EuclideanNorm
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# CORA's capsule–capsule `isIntersecting_`, as printed

`aux_isIntersecting_capsule` of `@capsule/isIntersecting_.m` (l. 103-143): the quadratic programme
in `(t₁, t₂)` with `H = 0.5*[g1'*g1 -g1'*g2; -g1'*g2 g2'*g2]` and `f = 2*[(c1-c2)'*g1;
-(c1-c2)'*g2]` over `[-1, 1]²`, the axis points `p1 = c1 + g1 x(1)`, `p2 = c2 + g2 x(2)`, and the
verdict `dist < r1 + r2 | withinTol(dist, r1 + r2)` (default tolerance `1e-8`; `withinTol`'s
relative test `|a-b|/min(|a|,|b|) <= tol` multiplied out). `CORAquadprog` (MOSEK's `mskqpopt` or
MATLAB's `quadprog`, both minimising `½ xᵀHx + fᵀx`) is the argument `quadprog H f lb ub`; the
theorems assume only that its output minimises that objective over the box. Kept only so that
`Capsule.isIntersecting_cora_counterexample` can state that it is unsound: the squared axis
distance is `xᵀMx + 2·(the linear term)` with `M` the bracket, so `H` needs `2 M`, not `½ M`.
`Capsule.isIntersecting_` is the sound test.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_isIntersecting_capsule(C1, C2)` as printed, `CORAquadprog` being `quadprog`. -/
def Capsule.isIntersectingCora
    (quadprog : Mat ℝ 2 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2 → Vec ℝ 2) (C₁ C₂ : Capsule n) : Prop :=
  let c1 := C₁.c
  let c2 := C₂.c
  let g1 := C₁.g
  let g2 := C₂.g
  let H : Mat ℝ 2 2 := (1 / 2 : ℝ) • !![g1 ⬝ᵥ g1, -(g1 ⬝ᵥ g2); -(g1 ⬝ᵥ g2), g2 ⬝ᵥ g2]
  let f : Vec ℝ 2 := (2 : ℝ) • ![(c1 - c2) ⬝ᵥ g1, -((c1 - c2) ⬝ᵥ g2)]
  let lb : Vec ℝ 2 := ![-1, -1]
  let ub : Vec ℝ 2 := ![1, 1]
  let x := quadprog H f lb ub
  let p1 := c1 + x 0 • g1
  let p2 := c2 + x 1 • g2
  let dist := ‖p1 - p2‖₂
  let combinedRadius := C₁.r + C₂.r
  let tol : ℝ := 1 / 10 ^ 8
  dist < combinedRadius ∨ |dist - combinedRadius| ≤ tol ∨
    |dist - combinedRadius| ≤ tol * min |dist| |combinedRadius|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
