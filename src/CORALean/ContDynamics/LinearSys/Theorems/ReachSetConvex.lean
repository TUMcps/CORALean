import CORALean.ContDynamics.LinearSys.Theorems.InputReachConvex
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq

/-!
# The time-point reachable set is convex

`reachSet_eq` makes it `e^{tA} R₀ ⊕ inputReach U t`, a linear image of a convex
set plus a convex one. [1, Sec. 4.2] uses it to read an inner approximation off
the convex hull of reachable support vectors, and [1]'s Sec. 5.2 to run GJK
against the reachable set.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: from a convex initial set under a convex bounded input set, the reachable
set at any `t ≥ 0` is convex. -/
theorem LinearSys.reachSet_convex (sys : LinearSys 𝕋 n) {R₀ U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hR₀ : Convex ℝ (construct R₀)) (hUconv : Convex ℝ (construct U))
    (hU : Bornology.IsBounded (construct U)) :
    Convex ℝ (sys.reachSet (Set.Icc 0 t) R₀ U t) :=
  sys.reachSet_eq R₀ U ht hU ▸
    (hR₀.linear_image (mulVecLin (exp (t • toRealMat sys.A)))).add
      (sys.inputReach_convex ht hUconv hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
