import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `reach_outer`, at the three system-matrix representations it now covers

Each is `:=` and nothing else: `reach_outer` was proved once, against `Mtimes`,
and elaborating here is the claim that the three instantiations in `Theorems.API`
are covered by it. `ℐ` and `𝕄𝒵` are the interval- and zonotope-matrix families
of `Interval.Real.Instances` and `Zonotope.Real.Instances`; `Mat ℝ` needs no
family notation, being already `ℕ → ℕ → Type`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

-- Anonymous, since their content is that they elaborate.

/-- §3.3.1: the system matrix bounded by an interval matrix. -/
example {n : ℕ} (sys : LinParamSysDT ℐ n) (o : ℕ) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) o R₀ U k) :=
  sys.reach_outer (S := 𝒵) o R₀ U traj k

/-- §3.3.2: the system matrix bounded by a matrix zonotope, strictly tighter
than an interval matrix, which throws away every correlation between entries. -/
example {n : ℕ} (sys : LinParamSysDT 𝕄𝒵 n) (o : ℕ) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) o R₀ U k) :=
  sys.reach_outer (S := 𝒵) o R₀ U traj k

/-- The point-matrix case, `𝕄 := Mat ℝ`: `LinearSysDT` again. -/
example {n : ℕ} (sys : LinParamSysDT (Mat ℝ) n) (o : ℕ) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) o R₀ U k) :=
  sys.reach_outer (S := 𝒵) o R₀ U traj k

end CORALean.Real
