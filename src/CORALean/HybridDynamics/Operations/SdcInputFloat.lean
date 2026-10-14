module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Interval.Float.Operations.SumTermsMat
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp

@[expose] public section

/-!
# A float box holding the constant flow [1, Prop. 1] chooses

`GuardMap.sdcInput`, `b = Θ(t)x₀ + Γ*(t)u_c`, `Θ(t) = ∑ᵢ₌₂^η Aⁱtⁱ⁻¹/i!`,
`Γ*(t) = ∑ᵢ₌₀^η Aⁱtⁱ/(i + 1)!`, CORA's `aux_constantFlow` [2], enclosed with directed rounding
for `t ≥ 0`: `Aⁱ` by `matPow` at the point interval matrix, `tᵖ/q!` between the corner products
of `[powDown, powUp]` and `invFactorialBounds`, the sums by `sumTermsMat` and the products with
`x₀` and `u_c` by `mtimesIntervalMat`. A caller takes one point of the box as its `b` and charges
the rest to its error.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
* [2] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_constantFlow`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 1]: a box holding `b = Θ(t)x₀ + Γ*(t)u_c`. -/
def GuardMap.sdcInputFloat (A : Mat 𝕋 n n) (uc : Vec 𝕋 n) (t : 𝕋) (η : ℕ) (x₀ : Vec 𝕋 n) :
    Interval (Vec 𝕋 n) :=
  let Apow : ℕ → Interval (Mat 𝕋 n n) := fun i =>                -- `Aⁱ`, bracketed
    Interval.matPow (Interval.point A) i
  let coefLo : ℕ → ℕ → 𝕋 := fun p q =>                           -- `tᵖ/q!`, down
    Interval.mulLo (powDown t p) (powUp t p) (MatExp.invFactorialBounds q).1
      (MatExp.invFactorialBounds q).2
  let coefHi : ℕ → ℕ → 𝕋 := fun p q =>                           -- and up
    Interval.mulHi (powDown t p) (powUp t p) (MatExp.invFactorialBounds q).1
      (MatExp.invFactorialBounds q).2
  let Θ := Interval.sumTermsMat (fun k =>                         -- `Θ = ∑ᵢ₌₂^η tⁱ⁻¹/i! Aⁱ`
    Interval.smul (coefLo (k + 1) (k + 2)) (coefHi (k + 1) (k + 2)) (Apow (k + 2))) (η - 1)
  let Γstar := Interval.sumTermsMat (fun k =>                     -- `Γ* = ∑ᵢ₌₀^η tⁱ/(i+1)! Aⁱ`
    Interval.smul (coefLo k (k + 1)) (coefHi k (k + 1)) (Apow k)) (η + 1)
  (Interval.mtimesIntervalMat Θ (Interval.point x₀)).plus        -- `Θx₀ + Γ*u_c`
    (Interval.mtimesIntervalMat Γstar (Interval.point uc))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
