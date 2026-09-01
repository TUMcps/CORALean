import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContSet.Zonotope.Real.API

/-!
# The step enclosure at a zonotope whose input set misses the origin

`timeInterval_outer_zonotope` needs `0 ∈ U`, which no zonotope has to satisfy.
A zonotope does, however, carry its own split for free: its centre is the
constant, and itself recentred is the part containing the origin. So the case
the thesis handles separately needs no extra input from the caller here.

`aux_segment c` is the segment from the origin to `c`, one generator wide. It is
what encloses the constant part, and is where this differs from the thesis —
see `InputSolutionTimeIntervalOuterSplit` for what `F̃` would buy instead.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

/-- The zonotope moved to the origin, keeping its generators. -/
def aux_centered (Z : Zonotope n) : Zonotope n := ⟨Z.h, 0, Z.G⟩

/-- The segment from the origin to `v`, as a zonotope. -/
noncomputable def aux_segment (v : Vec ℝ n) : Zonotope n :=
  ⟨1, fun i => v i / 2, fun i _ => v i / 2⟩

theorem aux_zero_mem_centered (Z : Zonotope n) :
    (0 : Vec ℝ n) ∈ (aux_centered Z).construct :=
  ⟨0, fun _ => by simp, fun _ => by simp [aux_centered]⟩

theorem aux_sub_mem_centered {Z : Zonotope n} {y : Vec ℝ n} (hy : y ∈ Z.construct) :
    y - Z.c ∈ (aux_centered Z).construct := by
  obtain ⟨β, hβ, hy⟩ := hy
  refine ⟨β, hβ, fun i => ?_⟩
  -- `(aux_centered Z).h` is `Z.h` only up to unfolding, which `simp` will not do
  -- inside the sum's binder
  simp only [aux_centered, Pi.sub_apply, Pi.zero_apply, zero_add, hy i, add_sub_cancel_left]
  rfl

theorem aux_zero_mem_segment (v : Vec ℝ n) : (0 : Vec ℝ n) ∈ (aux_segment v).construct :=
  ⟨fun _ => -1, fun _ => by norm_num, fun i => by simp [aux_segment]⟩

theorem aux_self_mem_segment (v : Vec ℝ n) : v ∈ (aux_segment v).construct :=
  ⟨fun _ => 1, fun _ => by norm_num, fun i => by simp [aux_segment]⟩

set_option maxHeartbeats 400000 in
/-- Every trajectory whose initial and input sets are zonotopes stays in the
step enclosure at every time of the step, with nothing assumed about where the
input set sits relative to the origin. -/
theorem LinearSys.Trajectory.timeInterval_outer_split_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀)
      (OuterContSet.plus (sys.inputSolution r (m + 2) (aux_segment U.c))
        (sys.inputSolution r (m + 2) (aux_centered U)))) :=
  traj.timeInterval_outer hr hε ht0 htr U.isBounded_construct
    (traj.inputSolution_timeInterval_outer_split hr (m + 2) hε
      (fun _ hy => aux_sub_mem_centered hy) (aux_self_mem_segment U.c)
      (aux_zero_mem_centered U) (aux_zero_mem_segment U.c)
      (aux_centered U).convex_construct (aux_centered U).isClosed_construct
      (aux_centered U).isBounded_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).convex_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isClosed_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isBounded_construct
      (aux_segment U.c).convex_construct (aux_segment U.c).isClosed_construct
      (aux_segment U.c).isBounded_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_segment U.c)).convex_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_segment U.c)).isClosed_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_segment U.c)).isBounded_construct
      ht0 htr)

end CORALean.Real
