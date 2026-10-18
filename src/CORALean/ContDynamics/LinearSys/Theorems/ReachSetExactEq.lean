module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactSubset
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactSuperset

@[expose] public section

/-!
# The reachable set is exactly the closed form

`reachSetExact` on `[0, t]`, evaluated at its right endpoint, equals
`e^{tA} R₀ ⊕ inputReach U t` outright: a trajectory is Carathéodory, so every
measurable input a witness in `inputReach` can name — a piecewise-constant one
among them — drives a run. This is what lets the layer refute as well as prove.
`ReachSetExactSubset`/`ReachSetExactSuperset` are the two halves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set at `t` is exactly `e^{tA} R₀ ⊕ inputReach U t`. -/
theorem LinearSys.reachSetExact_eq (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    sys.reachSetExact (Set.Icc 0 t) R₀ U t
      = (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀ + sys.inputReach U t :=
  Set.Subset.antisymm
    (sys.reachSetExact_subset_mulVecLin_image_add_inputReach R₀ U ht hU)
    (sys.mulVecLin_image_add_inputReach_subset_reachSetExact R₀ U ht hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
