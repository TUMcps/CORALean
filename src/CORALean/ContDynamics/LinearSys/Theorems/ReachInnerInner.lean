import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Definitions.ReachInner
import CORALean.ContDynamics.LinearSys.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetSubsetInputReach
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSuperset
import CORALean.ContDynamics.LinearSys.Theorems.ReachSubsetDiscretizeReachSetAddError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# An inner approximation of a continuous reachable set, over a whole run

`LinearSysDT.reachInner_inner` at the sample times of a continuous-time system,
and inside the *exact* reachable set there, not an enclosure of it: every point
of `reachInner` is the state at `t = kΔt` of a Carathéodory run of the system
from `R₀` under an input in `U`.

Three steps. `reach_subset_discretize_reachSet_add_error` measures the run
against the zero-order-hold reachable set, a recursion of zonotopes and so
convex and compact, which is what `reachSet_inner_of_outer` asks of it. That set
lies in `e^{kΔtA} R₀ ⊕ inputReach U (kΔt)`, a piecewise-constant input being
admissible (`discretize_reachSet_subset_inputReach`). And that sum is `reachSet`
(`reachSet_eq`), the integral equation admitting the jumps such an input makes.

The hypotheses are the step's own: `0 < Δt`, and the truncation order large
enough that the exponential's remainder bound converges. `R₀` and `U` are
zonotopes, so nonempty, convex, compact and bounded without being asked.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sampled run minus its own accumulated error is *contained in* the states
the system reaches at `t = kΔt`. -/
theorem LinearSys.reachInner_inner (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    sys.reachInner Δt η o ho R₀ U k
      ⊆ sys.reachSet (S := 𝒵) (Set.Icc 0 ((k : ℝ) * Δt)) R₀ U
          ((k : ℝ) * Δt) := by -- --- PROOF ---
  set Q := Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U with hQ
  -- the run minus its error lies in the zero-order-hold reachable set
  have hinner := (sys.discretize Δt).reachSet_inner_of_outer (S := 𝒵)
    (Zonotope.convex_construct R₀) (Zonotope.isCompact_construct R₀)
    (Zonotope.convex_construct Q) (Zonotope.isCompact_construct Q) k
    ⟨_, Zonotope.centre_mem_construct _⟩ (Zonotope.isBounded_construct _)
    (sys.reach_subset_discretize_reachSet_add_error hΔt η hε ho R₀ U k)
  -- each step's held input is `stepInputConst` at a point of `U`
  have hstep : construct Q ⊆ (fun c => sys.stepInputConst c Δt) '' construct U := by
    intro v hv
    have hv' : v ∈ Q.construct := hv
    rw [hQ, ← Zonotope.mtimes_exact] at hv'
    obtain ⟨c, hc, rfl⟩ := hv'
    exact ⟨c, hc, rfl⟩
  have hzoh := sys.discretize_reachSet_subset_inputReach (S := 𝒵) hΔt R₀ U Q
    (Zonotope.isBounded_construct U) ⟨_, Zonotope.centre_mem_construct U⟩ hstep k
  exact hinner.trans (hzoh.trans (sys.mulVecLin_image_add_inputReach_subset_reachSet
    (S := 𝒵) R₀ U (by positivity) (Zonotope.isBounded_construct U)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
