import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulVecEqOfNormLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSubPeanoBakerSumLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerTermMemMatPow
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

/-!
# A run inside a box is mapped by a member of the box's exponential enclosure

`exp_mem_expIntervalEnclosure` for a matrix that varies in time. A solution of
`x(s) = x(0) + ∫₀ˢ A(σ) x(σ) dσ` on `[0, t]`, every `A(σ)` in `B`, reaches
`x(t) = Φ x(0)` for some `Φ ∈ expIntervalEnclosure (t • B) η` — the very
interval matrix `'constParam'` uses, so CORA's `'varParam'` mapping matrix
(`expmIndMixed` in `priv_mappingMatrix`) needs nothing wider.

`Φ` is the first `η + 1` Peano–Baker terms plus a correction. Their sum lies in
`expIntervalTaylor (t • B) η` term by term (`peanoBakerTerm_mem_matPow`), and what
it misses of `x(t)` is a vector of norm at most `‖x(0)‖` times the remainder bound
(`norm_sub_peanoBakerSum_le`). Any such vector is `E x(0)` for a matrix `E` whose
entries are within that bound — one column, the one where `x(0)` attains its sup
norm — and `E` is exactly the widening `expIntervalEnclosure` adds.

`Φ` depends on `x(0)`, as no single matrix maps a time-varying run's every start.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The first `η + 1` terms at `t` lie in the interval Taylor truncation of `t • B`. -/
theorem aux_peanoBakerSum_mem {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {t : ℝ} (ht : 0 ≤ t) (η : ℕ) :
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of the integral equation at a matrix that stays in `B` is mapped,
at time `t`, by a member of `B`'s exponential enclosure over the step `t`. -/
theorem MatExp.exists_mem_expIntervalEnclosure_of_integral {B : Interval (Mat ℝ n n)}
    {A : ℝ → Mat ℝ n n} (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct)
    {x : ℝ → Vec ℝ n} {t : ℝ} (ht : 0 ≤ t) (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) (η : ℕ)
    (hε : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1) :
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
