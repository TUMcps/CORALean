module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachInnerInner
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner

@[expose] public section

/-!
# `reachInnerRep` is an inner approximation, as a representation

What `reachInner_inner` guarantees about a `Set`, carried to a zonotope a later
step could take as input: `minkDiffRep_inner` puts the returned zonotope inside
the Minkowski difference, and that difference *is* `reachInner`.

`M` is the caller's, and is the only thing left to choose; a wrong one gives
`none`. The zonotope returned can also be a point, where the accumulated error
has nearly outgrown the run — a statement about the enclosures and reductions,
not about the system.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `reachInnerRep` returns is inside the states the system reaches at
`t = kΔt`. -/
theorem LinearSys.reachInnerRep_inner (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin ((sys.discretize Δt).reach (S := 𝒵) ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩
      ⟨o, ho⟩).h → Fin (sys.reachError Δt η o ho R₀ U k).h → ℝ) {D : Zonotope (Vec ℝ n)}
    (hD : sys.reachInnerRep Δt η o ho R₀ U k M = some D) :
    construct D ⊆ sys.reachSet (S := 𝒵) (Set.Icc 0 ((k : ℝ) * Δt)) R₀ U ((k : ℝ) * Δt) :=
  (Zonotope.minkDiffRep_inner _ _ M hD).trans (sys.reachInner_inner hΔt η hε ho R₀ U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
