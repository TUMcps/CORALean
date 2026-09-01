import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContSet.Zonotope.Real.API

/-!
# The step enclosure at a zonotope whose input set misses the origin

`timeInterval_outer_zonotope` needs `0 ∈ U`, which no zonotope has to satisfy.
A zonotope carries everything the split needs for free: its centre is the
constant, itself recentred is the part holding the origin, and a zonotope with
no generators or with one gives the point and the segment the constant part is
enclosed against.

So Althoff's second case costs the caller nothing here — the statement assumes
nothing at all about where the input set sits.
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

/-- A single point, as a zonotope with no generators. -/
def aux_point (v : Vec ℝ n) : Zonotope n := ⟨0, v, fun _ _ => 0⟩

/-- The segment from the origin to `v`, as a zonotope with one generator. -/
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

theorem aux_self_mem_point (v : Vec ℝ n) : v ∈ (aux_point v).construct :=
  ⟨0, fun j => j.elim0, fun i => by simp [aux_point]⟩

theorem aux_smul_mem_segment (v : Vec ℝ n) {lam : ℝ} (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
    lam • v ∈ (aux_segment v).construct := by
  refine ⟨fun _ => 2 * lam - 1, fun _ => ?_, fun i => ?_⟩
  · rw [abs_le]
    constructor <;> [linarith [hlam.1]; linarith [hlam.2]]
  · -- `(aux_segment v).h` is `1` only up to unfolding, which leaves the sum's
    -- binder type unreduced for `simp`
    show lam * v i = v i / 2 + ∑ _j : Fin 1, v i / 2 * (2 * lam - 1)
    rw [Fin.sum_univ_one]
    ring

set_option maxHeartbeats 400000 in
/-- Every trajectory whose initial and input sets are zonotopes stays in the
step enclosure at every time of the step, wherever the input set sits. -/
theorem LinearSys.Trajectory.timeInterval_outer_split_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀)
      (OuterContSet.plus
        (OuterContSet.plus
          (Mtimes.mtimes (IntervalMat.expIntegral (toRealMat sys.A) r) (aux_segment U.c))
          (Mtimes.mtimes
            (IntervalMat.constCorrectionMatrix (toRealMat sys.A) r (m + 2)) (aux_point U.c)))
        (sys.inputSolution r (m + 2) (aux_centered U)))) :=
  traj.timeInterval_outer hr hε ht0 htr U.isBounded_construct
    (traj.inputSolution_timeInterval_outer_split hr (m + 2) hε
      (fun _ hy => aux_sub_mem_centered hy) (aux_self_mem_point U.c)
      (fun _ hlam => aux_smul_mem_segment U.c hlam)
      (aux_point U.c).isBounded_construct
      (aux_zero_mem_centered U)
      (aux_centered U).convex_construct (aux_centered U).isClosed_construct
      (aux_centered U).isBounded_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).convex_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isClosed_construct
      (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isBounded_construct
      ht0 htr)

end CORALean.Real
