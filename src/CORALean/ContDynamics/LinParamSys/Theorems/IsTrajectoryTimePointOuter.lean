module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryExistsIntegralEq
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulVecEqOfNormLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSubPeanoBakerSumLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerTermMemMatPow
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# Where an input-free time-varying run is at a time of its window

`IsCanonicalTrajectory.aux_exists_mem_expIntervalEnclosure` read at the sets: the box's
exponential enclosure over `t` times the initial set holds the run's state at
`t`. CORA's `'varParam'` homogeneous solution at a time point, the mapping matrix
of `priv_mappingMatrix` applied to the initial set; the same set
`LinParamSys.timeInterval` starts from at `'constParam'`.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `A` – matrix signal
* `t` – time
* `η` – Taylor order

## Hypotheses
* `traj` – time-varying trajectory
* `ht` – time nonnegative
* `hT` – window lies in the time set
* `hu` – input vanishes on the window
* `hε` – order admissible

## Conclusion
* the state at `t` lies in the exponential enclosure applied to the initial set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
section
open MeasureTheory
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The first `η + 1` terms at `t` lie in the interval Taylor truncation of `t • B`. -/
private theorem aux_peanoBakerSum_mem {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {t : ℝ} (ht : 0 ≤ t) (η : ℕ) : -- --- CONCL ---
    ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t
      ∈ (MatExp.expIntervalTaylor (Interval.smul t B) η).construct := by -- --- PROOF ---
  -- each term is `1/k!` times a member of the `k`-th box power
  have hterm : ∀ k, MatExp.peanoBakerTerm A k t ∈ (Interval.smul ((Nat.factorial k : ℝ)⁻¹)
      (Interval.matPow (Interval.smul t B) k)).construct := fun k => by
    have h := Interval.smul_outer ((Nat.factorial k : ℝ)⁻¹) _
      (MatExp.peanoBakerTerm_mem_matPow hA hAB k ht)
    rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h
  induction η with
  | zero => rw [Finset.sum_range_one]; exact hterm 0
  | succ k ih =>
    have h := Interval.plus_outer _ _ (Set.add_mem_add (hterm (k + 1)) ih)
    rw [add_comm (MatExp.peanoBakerTerm A (k + 1) t), ← Finset.sum_range_succ] at h
    exact h


/-- A solution of the integral equation at a matrix that stays in `B` is mapped,
at time `t`, by a member of `B`'s exponential enclosure over the step `t`. -/
private theorem MatExp.aux_exists_mem_expIntervalEnclosure_of_integral {B : Interval (Mat ℝ n n)}
    {A : ℝ → Mat ℝ n n} (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct)
    {x : ℝ → Vec ℝ n} {t : ℝ} (ht : 0 ≤ t) (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) (η : ℕ)
    (hε : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    ∃ Φ ∈ (MatExp.expIntervalEnclosure (Interval.smul t B) η).construct,
      x t = Φ *ᵥ x 0 := by -- --- PROOF ---
  set T := ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t with hT
  set R := MatExp.expRemainderBound (Interval.smul t B).absMax η with hRdef
  have hR0 : 0 ≤ R := by
    have h1 : 0 < 1 - ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) := by linarith
    rw [hRdef, MatExp.expRemainderBound]; positivity
  -- what the truncation misses is a short vector, so a matrix within the radius
  have hρ := MatExp.norm_sub_peanoBakerSum_le hA hAB ht hxc hx η hε
  rw [← Matrix.sum_mulVec, ← hT] at hρ
  obtain ⟨E, hE, hEv⟩ := exists_mulVec_eq_of_norm_le hR0 hρ
  refine ⟨T + E, Interval.mem_mat_iff.mpr fun i j => ?_, ?_⟩
  · have hTm := Interval.mem_mat_iff.mp (aux_peanoBakerSum_mem hA hAB ht η) i j
    have hEij := abs_le.mp (hE i j)
    show (MatExp.expIntervalTaylor _ η).inf i j - R ≤ (T + E) i j ∧
      (T + E) i j ≤ (MatExp.expIntervalTaylor _ η).sup i j + R
    rw [Matrix.add_apply]
    constructor <;> linarith [hTm.1, hTm.2, hEij.1, hEij.2]
  · rw [Matrix.add_mulVec, hEv]; abel

end
end Real


section
open MeasureTheory
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

omit [Mtimes ℐ S] in
/-- An input-free `'varParam'` run, at a time `t` of its window, is its start
mapped by a member of the box's exponential enclosure over `t`. -/
private theorem LinParamSys.IsCanonicalTrajectory.aux_exists_mem_expIntervalEnclosure
    {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) (η : ℕ)
    (hε : ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    ∃ Φ ∈ construct (MatExp.expIntervalEnclosure (Interval.smul t sys.A) η),
      x t = Φ *ᵥ x 0 := by -- --- PROOF ---
  obtain ⟨Â, hÂi, hÂB, hx⟩ := traj.exists_integral_eq ht hT hu
  have hxc : ContinuousOn x (Set.Icc 0 t) := traj.cont.mono hT
  exact MatExp.aux_exists_mem_expIntervalEnclosure_of_integral hÂi hÂB ht hxc hx η hε

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run is, at every time `t` of its window, in the
box's exponential enclosure over `t` times the initial set. -/
theorem LinParamSys.IsCanonicalTrajectory.timePoint_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) (η : ℕ)
    (hε : ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    x t ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.expIntervalEnclosure (Interval.smul t sys.A) η) R₀) := by -- --- PROOF ---
  obtain ⟨Φ, hΦ, hx⟩ := traj.aux_exists_mem_expIntervalEnclosure ht hT hu η hε
  rw [hx]
  exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hΦ (Set.mem_image_of_mem _ traj.init))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
