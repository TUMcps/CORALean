module

public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
public import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope
public import CORALean.HybridDynamics.Theorems.InputSetOuter
public import CORALean.HybridDynamics.Theorems.InputSetFloatOuter

@[expose] public section

/-!
# `HybridDynamics/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

section

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)] {L 𝕋 : Type}
  [Scalar 𝕋] {n : ℕ}


-- ============================  `Location.Trajectory.inputSet_mem`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The combined input of a stay lies in `inputSet` at every time of the stay. -/
theorem Location.Trajectory.inputSet_mem {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x u w}
    (traj : ℓ.Trajectory τ x u w) : ∀ t ∈ Set.Icc 0 τ, toRealMat ℓ.dynamics.B *ᵥ u t +
      toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w t ∈ construct ℓ.inputSet :=
  fun t ht => ℓ.inputSet_outer (traj.input t ht) (traj.dist t ht)

end

section

open Matrix ContSet Scalar
open scoped CORALean.Float

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Float.FloatOps 𝕋]
  [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =========================  `Location.Trajectory.inputSetFloat_mem`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The combined input of a stay lies in `inputSetFloat` at every time of the stay. -/
theorem Location.Trajectory.inputSetFloat_mem {ℓ : Location 𝒵[𝕋] G L 𝕋 n} {τ : ℝ} {x u w}
    (traj : ℓ.Trajectory τ x u w) : ∀ t ∈ Set.Icc 0 τ, toRealMat ℓ.dynamics.B *ᵥ u t +
      toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w t ∈ construct ℓ.inputSetFloat :=
  fun t ht => ℓ.inputSetFloat_outer (traj.input t ht) (traj.dist t ht)

end

section

variable {G P : ℕ → Type} {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================  `NonlinearReset.evaluate_toNonlinearReset`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- At every point, `evaluate` of `Transition.toNonlinearReset` is `Transition.reset`: the nonlinear
reset class contains the affine one, whatever the input. -/
theorem NonlinearReset.evaluate_toNonlinearReset (e : Transition G L 𝕋 n) (x : Vec ℝ n)
    (u : Vec ℝ 0) : e.toNonlinearReset.evaluate x u = e.reset x := rfl


-- ============================  `Transition.guard2polytope_reset`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The reset is untouched, so it is the same map. -/
theorem Transition.guard2polytope_reset (conv : G n → P n) (e : Transition G L 𝕋 n) :
    (e.guard2polytope conv).reset = e.reset := rfl

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
