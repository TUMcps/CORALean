module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Continuous-time linear systems: the classical run

A run whose state has a derivative at every point of `T`, taken within `T`
itself and so two-sided wherever `T` is: within `Ici t` it would be a right
derivative everywhere, which does not force continuity. `u` needs no
regularity here, being pinned by `u t = ẋ(t) - A x(t)` wherever the flow holds.

This was `IsTrajectory` before the Carathéodory reading replaced it. It stays as
the special case a nonlinear or parameter-varying run is first linearized to,
classically, and `IsCanonicalClassicalTrajectory.trajectory` hands each such run to every
guarantee stated over `IsTrajectory`. It excludes a zero-order-hold input, whose
jumps have no two-sided derivative, so nothing reached is stated over it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A run of `sys` on `T` whose state has the derivative `A x + u` at every
point of `T`, within `T`. -/
structure LinearSys.IsCanonicalClassicalTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
