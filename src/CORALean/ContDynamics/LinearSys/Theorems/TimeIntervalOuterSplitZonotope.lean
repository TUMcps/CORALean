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

So Althoff's second case assumes nothing at all about where the input set sits.
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
def aux_centered (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) := ⟨Z.h, 0, Z.G⟩

/-- A single point, as a zonotope with no generators. -/
def aux_point (v : Vec ℝ n) : Zonotope (Vec ℝ n) := ⟨0, v, Fin.elim0⟩

/-- The segment from the origin to `v`, as a zonotope with one generator. -/
noncomputable def aux_segment (v : Vec ℝ n) : Zonotope (Vec ℝ n) :=
  ⟨1, (2:ℝ)⁻¹ • v, fun _ => (2:ℝ)⁻¹ • v⟩

-- each of these states its own `h`, which is that count only up to unfolding, so
-- the sum's binder needs a `show` to reduce

theorem aux_zero_mem_centered (Z : Zonotope (Vec ℝ n)) :
    (0 : Vec ℝ n) ∈ (aux_centered Z).construct := by
  refine ⟨0, fun _ => by simp, ?_⟩
  show (0 : Vec ℝ n) = 0 + ∑ j, (0 : Fin Z.h → ℝ) j • Z.G j
  simp

theorem aux_sub_mem_centered {Z : Zonotope (Vec ℝ n)} {y : Vec ℝ n} (hy : y ∈ Z.construct) :
    y - Z.c ∈ (aux_centered Z).construct := by
  obtain ⟨β, hβ, hy⟩ := hy
  refine ⟨β, hβ, ?_⟩
  rw [hy]
  show Z.c + ∑ j, β j • Z.G j - Z.c = 0 + ∑ j, β j • Z.G j
  abel

theorem aux_self_mem_point (v : Vec ℝ n) : v ∈ (aux_point v).construct := by
  refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
  show v = v + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

theorem aux_smul_mem_segment (v : Vec ℝ n) {lam : ℝ} (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
    lam • v ∈ (aux_segment v).construct := by
  refine ⟨fun _ => 2 * lam - 1, fun _ => ?_, ?_⟩
  · rw [abs_le]
    constructor <;> [linarith [hlam.1]; linarith [hlam.2]]
  · show lam • v = (2:ℝ)⁻¹ • v + ∑ _j : Fin 1, (2 * lam - 1) • ((2:ℝ)⁻¹ • v)
    rw [Fin.sum_univ_one, smul_smul]
    match_scalars
    ring

set_option maxHeartbeats 400000 in
/-- Every trajectory whose initial and input sets are zonotopes stays in the
step enclosure at every time of the step, wherever the input set sits. -/
theorem LinearSys.Trajectory.timeInterval_outer_split_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope (Vec ℝ n)} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory (S := 𝒵) R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (OuterContSet.plus
      (sys.timeIntervalStep (S := 𝒵) r (m + 2) R₀)
      (OuterContSet.plus
        (OuterContSet.plus
          (Mtimes.mtimes (𝕄 := Mat ℝ) (S := 𝒵)
            (MatExp.expIntegral (toRealMat sys.A) r) (aux_segment U.c))
          (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵)
            (MatExp.constCorrectionMatrix (toRealMat sys.A) r (m + 2)) (aux_point U.c)))
        (sys.inputSolution (S := 𝒵) r (m + 2) (aux_centered U)))) :=
  traj.timeInterval_outer hr hε ht0 htr U.isBounded_construct
    (traj.inputSolution_timeInterval_outer_split hr (m + 2) hε
      (fun _ hy => aux_sub_mem_centered hy) (aux_self_mem_point U.c)
      (fun _ hlam => aux_smul_mem_segment U.c hlam)
      (aux_point U.c).isBounded_construct
      (aux_zero_mem_centered U)
      (aux_centered U).convex_construct (aux_centered U).isClosed_construct
      (aux_centered U).isBounded_construct
      (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).convex_construct
      (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isClosed_construct
      (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
        (aux_centered U)).isBounded_construct
      ht0 htr)

end CORALean.Real
