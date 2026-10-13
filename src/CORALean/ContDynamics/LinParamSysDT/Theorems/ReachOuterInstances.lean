import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `reach_outer`, at the four system-matrix representations it now covers

Each is `:=` and nothing else: `reach_outer` was proved once, against `Mtimes`,
and elaborating here is the claim that the four instantiations in `Theorems.API`
are covered by it. `ℐ`, `𝕄𝒵` and `𝕄𝒫` are the interval-, zonotope- and
polytope-matrix families of `Interval.Real.Instances`, `Zonotope.Real.Instances`
and `VPolytope.Real.Instances`; `Mat ℝ` needs no family notation, being already
`ℕ → ℕ → Type`. `𝕄𝒫`'s set family is `VPolytope`, the only one of the four not
built on a zonotope.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---

namespace CORALean

open CORALean.Real
open Matrix ContSet

-- Anonymous, since their content is that they elaborate.

/-- §3.3.1: the system matrix bounded by an interval matrix. -/
example {n : ℕ} (sys : LinParamSysDT ℐ n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := 𝒵) ho R₀ U traj k

/-- §3.3.2: the system matrix bounded by a matrix zonotope, strictly tighter
than an interval matrix, which throws away every correlation between entries. -/
example {n : ℕ} (sys : LinParamSysDT 𝕄𝒵 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := 𝒵) ho R₀ U traj k

/-- The point-matrix case, `𝕄 := Mat ℝ`: `LinearSysDT` again. -/
example {n : ℕ} (sys : LinParamSysDT (Mat ℝ) n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := 𝒵) ho R₀ U traj k

/-- §3.3.3: the system matrix bounded by a matrix polytope, the only one of
the four whose set family is not `𝒵`. -/
example {n : ℕ} (sys : LinParamSysDT 𝕄𝒫 n) {o : ℕ} (ho : 0 < o) (R₀ U : VPolytope (Vec ℝ n))
    {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := fun n => VPolytope (Vec ℝ n)) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := fun n => VPolytope (Vec ℝ n)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := fun n => VPolytope (Vec ℝ n)) ho R₀ U traj k

end CORALean
