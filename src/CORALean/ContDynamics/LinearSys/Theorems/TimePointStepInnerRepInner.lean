module

public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInnerSubsetReachSetExact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono
public import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallSubsetDiagonal
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner

@[expose] public section

/-!
# `timePointStepInnerRep` is an inner approximation, as a representation

`minkDiffRep_inner` puts the returned zonotope inside the step minus its error
box. The box contains the error ball (`closedBall_subset_diagonal`), and a
Minkowski difference is antitone in what it takes off, so that difference lies
inside `timePointStepInner`, which `timePointStepInner_subset_reachSetExact`
places in the exact reachable set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `timePointStepInnerRep` returns is inside the states the system
reaches at `t = r`. -/
theorem LinearSys.timePointStepInnerRep_inner (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ U : Zonotope (Vec ℝ n))
    (M : Fin (sys.timePointStep (S := 𝒵) r η X₀ U).h →
      Fin (sys.timePointStepErrorBox r η U).h → ℝ) {D : Zonotope (Vec ℝ n)}
    (hD : sys.timePointStepInnerRep r η X₀ U M = some D) : -- --- CONCL ---
    construct D ⊆ sys.reachSetExact (S := 𝒵) (Set.Icc 0 r) X₀ U r :=
  ((Zonotope.minkDiffRep_inner _ _ M _ hD).trans
    (minkowskiDiff_mono subset_rfl (Zonotope.closedBall_subset_diagonal _))).trans
    (sys.timePointStepInner_subset_reachSetExact hr η hε X₀ U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
