module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiff
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# The inner algorithm's time-interval output holds an unreachable state

[1, Alg. 1] ensures that its output `R̂(τ) = ⋃_k R̂(τ_k)` is an inner approximation of the
reachable set over `[0, t_end]`; line 16 computes `R̂(τ_k)` by `Prop. 2`, which is false for a
convex initial set as well (`convexHull_timeInterval_convex_counterexample`), and the algorithm
inherits it. One step, `t_end = 1`, `ω = 1`, of the shear `ẋ = (x₂, 0)` from the box
`X₀ = [-1/10, 1/10] × [-1, 1]`, a polytope as line 1 requires: with the box's center `0` as
`cen(X₀)`, line 4 gives `x* = 0`, line 5 `w = 0` and `A = [0 1; 0 0]`, line 6 `C = 0`
(`F(1) = 0` and `w = 0`, since `A² = 0`), the field has no Lagrange remainder, so lines 9-13
stop at `L̂ = 0` and line 14 gives `R̂_err(L̂) = 0` and `c = 0`. Line 16 is then
`conv(X₀, e^{A}X₀)`, which holds `(1/2, 0)`, the midpoint of `(0, -1)` and `e^{A}(0, 1) = (1, 1)`,
and no run from `X₀` passes through `(1/2, 0)` in `[0, 1]`: one through it starts on `x₂ = 0`,
where `ẋ = 0`, so its first coordinate stays in `[-1/10, 1/10]`.

The subroutines enter only through what (6), (9), (13), (17) and the center give for this
system, stated as hypotheses on `ops`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s output `R̂(τ)` for the shear `ẋ = (x₂, 0)` from `[-1/10, 1/10] × [-1, 1]` over
`[0, 1]` in one step holds `(1/2, 0)`, which no run reaches at any `t ∈ [0, 1]`. -/
theorem NonlinearSys.innerMinkDiff_timeInterval_counterexample
    (ops : NonlinearSys.InnerMinkDiffOps 2 𝓛) (fuel : ℕ) (hfuel : 0 < fuel)
    (U : Set (Vec ℝ 1)) :
    let sys : NonlinearSys 2 1 := ⟨fun x _ => ![x 1, 0], 2, fun x _ => x⟩
    let A : Mat ℝ 2 2 := !![0, 1; 0, 0]
    let X₀ : Set (Vec ℝ 2) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    ops.cen X₀ = 0 → (∀ x, ops.jac x = A) → (∀ B, ops.curv 1 A B 0 = {0}) →
    ops.smul (11 / 10) ops.zero = ops.zero → ops.err 1 A ops.zero = {0} →
    (∀ x D, ops.lagr x D = ops.zero) → ops.sub ops.zero ops.zero = true → ops.cen {0} = 0 →
    ∃ Rτ, NonlinearSys.innerMinkDiff ops (fun x => sys.f x 0) X₀ 1 1 fuel = some Rτ ∧
      ![1 / 2, 0] ∈ Rτ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ![1 / 2, 0] ∉ sys.reachSet (S := 𝒮) (Icc 0 t) X₀ U
          t := by -- --- PROOF ---
  intro sys A X₀ hcen hjac hC hsmul herr hlagr hsub hcen0
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hf0 : sys.f 0 0 = 0 := by
    ext i; fin_cases i <;> rfl
  have hmd : ∀ T : Set (Vec ℝ 2), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  -- `e^{A} = I + A`, as `A² = 0`
  have hA2 : A ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hexp : exp ((1 : ℝ) • A) = 1 + A := by
    rw [one_smul, exp_eq_tsum ℝ]
    show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • A ^ i = 1 + A
    rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
      rw [pow_eq_zero_of_le (by simp at hb; omega) hA2, smul_zero]]
    simp [Finset.sum_range_succ]
  -- what one step computes
  have hrun : NonlinearSys.innerMinkDiff ops (fun x => sys.f x 0) X₀ 1 1 (k + 1) =
      some (∅ ∪ convexHull ℝ (X₀ ∪ (fun x => exp ((1 : ℝ) • A) *ᵥ x) '' X₀)) := by
    simp [NonlinearSys.innerMinkDiff, NonlinearSys.innerMinkDiffLoop,
      NonlinearSys.innerMinkDiffStep, NonlinearSys.innerMinkDiffRemainder, hcen, hf0, hjac, hC,
      hsmul, herr, hlagr, hsub, hcen0, hmd]
  -- membership in the box, coordinatewise
  have hmem : ∀ y : Vec ℝ 2, y ∈ X₀ ↔ y 0 ∈ Icc (-1 / 10) (1 / 10) ∧ y 1 ∈ Icc (-1) 1 := by
    intro y
    simp only [X₀, mem_Icc, Pi.le_def, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  refine ⟨_, hrun, Or.inr ?_, fun t ht => ?_⟩
  · -- the midpoint of `(0, -1) ∈ X₀` and `(1, 1) = e^{A}(0, 1)`
    have h0 : (![0, -1] : Vec ℝ 2) ∈ X₀ ∪ (fun x => exp ((1 : ℝ) • A) *ᵥ x) '' X₀ :=
      Or.inl ((hmem _).mpr ⟨by simp; norm_num, by simp⟩)
    have h1 : (![1, 1] : Vec ℝ 2) ∈ X₀ ∪ (fun x => exp ((1 : ℝ) • A) *ᵥ x) '' X₀ := by
      refine Or.inr ⟨![0, 1], (hmem _).mpr ⟨by simp; norm_num, by simp⟩, ?_⟩
      simp only [hexp, Matrix.add_mulVec, Matrix.one_mulVec]
      ext i; fin_cases i <;> simp [A]
    refine segment_subset_convexHull h0 h1
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp
  · -- a run through `(1/2, 0)` starts on `x₂ = 0` and keeps its first coordinate
    rintro ⟨x, u, traj, hxt⟩
    have hder : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt x ![x s 1, 0] (Icc 0 t) s :=
      fun s hs => traj.flow s hs
    -- a function with zero derivative on `[0, t]` is constant there
    have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt g 0 (Icc 0 t) s) →
        ∀ s ∈ Icc (0 : ℝ) t, g s = g 0 := fun g hd =>
      constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
        (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
    have htt : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
    -- the run is `x s = (x₀₁ + s x₀₂, x₀₂)` on `[0, t]`
    have h1 : x t 1 = x 0 1 :=
      hconst (fun s => x s 1) (fun s hs => by simpa using hasDerivWithinAt_pi.mp (hder s hs) 1)
        t htt
    have h0 : x t 0 - t * x 0 1 = x 0 0 - 0 * x 0 1 :=
      hconst (fun s => x s 0 - s * x 0 1) (fun s hs => by
        have hx : HasDerivWithinAt (fun s => x s 0) (x s 1) (Icc 0 t) s := by
          simpa using hasDerivWithinAt_pi.mp (hder s hs) 0
        have h3 := hx.sub ((hasDerivWithinAt_id s (Icc 0 t)).mul_const (x 0 1))
        rwa [hconst (fun s => x s 1) (fun s hs => by
          simpa using hasDerivWithinAt_pi.mp (hder s hs) 1) s hs, one_mul, sub_self] at h3)
        t htt
    have e1 := congrFun hxt 1
    have e0 := congrFun hxt 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have hb := ((hmem (x 0)).mp traj.init).1
    -- so `x₀₂ = 0` and `x₀₁ = 1/2`, outside `[-1/10, 1/10]`
    rw [e1] at h1
    rw [e0, ← h1, mul_zero, zero_mul, sub_zero, sub_zero] at h0
    rw [← h0] at hb
    norm_num at hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
