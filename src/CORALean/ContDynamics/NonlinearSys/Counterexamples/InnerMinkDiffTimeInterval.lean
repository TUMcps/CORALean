module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiff
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpSmulShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerAbstrErrShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerCurvatureErrorShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerLagrangeRemainderShear
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# The inner algorithm's time-interval output holds an unreachable state

[1, Alg. 1] ensures that its output `R̂(τ) = ⋃_k R̂(τ_k)` is an inner approximation of the reachable
set over `[0, t_end]`; line 16 computes `R̂(τ_k)` by `Prop. 2`, false for a convex `X₀` as well.
One step, `t_end = ω = 1`, of the shear `ẋ = (x₂, 0)` from `X₀ = [-1/10, 1/10] × [-1, 1]`, Taylor
order `η ≥ 1`, `cen(X₀) = 0`: `x* = 0`, `w = 0`, `A = [0 1; 0 0]`, `A² = 0`, so `E` and `F` vanish
and `C = {0}` (17); `D²f ≡ 0`, so `L̂ = 0` (9), `R̂_err = {0}` (13), `c = 0`. Line 16 is
`conv(X₀, e^{A}X₀)`, holding `(1/2, 0)`, which no run passes through in `[0, 1]`. At `η = 0`,
`E = |A|Δt = A` and `C = [-1, 1] × {0}` is wider than the box and its shear, so both Minkowski
differences are empty and the claim holds. `curv`, `err`, `lagr` are (17), (13), (9) as printed.

## Inputs
* `ops` – subroutine operations
* `η` – Taylor order
* `fuel` – iteration bound
* `U` – input set

## Hypotheses
* `hη` – Taylor order positive
* `hfuel` – iteration bound positive
* `hcen` – the box's center, a Chebyshev center of it, is `cen(X₀)`
* `hcen0` – a point is its own center
* `hbox` – the box of Sec. II-A encloses `X₀`
* `hjac` – (6): the field is linear, its Jacobian `A` everywhere
* `hcurv` – `curv` is the curvature error (17)
* `herr` – `err` is the abstraction error (13)
* `hlagr` – `lagr` is the Lagrange remainder (9) of the field
* `hzero` – line 9's interval `[0, 0]` is the set `{0}`
* `hsmul` – line 11's `μL` scales the set
* `hsub` – line 13's test is the inclusion `L ⊆ L̂`

## Conclusion
* the algorithm's output holds a state no run reaches

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Pointwise Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s output `R̂(τ)` for the shear `ẋ = (x₂, 0)` from `[-1/10, 1/10] × [-1, 1]` over
`[0, 1]` in one step, at any Taylor order `η ≥ 1`, holds `(1/2, 0)`, which no run reaches at any
`t ∈ [0, 1]`; `curv`, `err` and `lagr` are (17), (13) and (9), their values derived. -/
theorem NonlinearSys.innerMinkDiff_timeInterval_counterexample
    (ops : NonlinearSys.InnerMinkDiffOps 2 (Set (Vec ℝ 2))) (η : ℕ) (hη : 1 ≤ η) (fuel : ℕ)
    (hfuel : 0 < fuel) (U : Set (Vec ℝ 1))
    (hcen : ops.cen (Icc ![-1 / 10, -1] ![1 / 10, 1]) = 0) (hcen0 : ops.cen {0} = 0)
    (hbox : Icc ![-1 / 10, -1] ![1 / 10, 1] ⊆ ops.box (Icc ![-1 / 10, -1] ![1 / 10, 1]))
    (hjac : ∀ x, ops.jac x = !![0, 1; 0, 0]) (hcurv : ops.curv = NonlinearSys.innerCurvatureError η)
    (herr : ops.err = NonlinearSys.innerAbstrErr η)
    (hlagr : ops.lagr = NonlinearSys.innerLagrangeRemainder fun x => ![x 1, 0])
    (hzero : ops.zero = {0}) (hsmul : ∀ μ L, ops.smul μ L = μ • L)
    (hsub : ∀ L L', ops.sub L L' = true ↔ L ⊆ L') : -- --- CONCL ---
    let sys : NonlinearSys 2 1 := ⟨fun x _ => ![x 1, 0], 2, fun x _ => x⟩
    let X₀ : Set (Vec ℝ 2) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    ∃ Rτ, NonlinearSys.innerMinkDiff ops (fun x => sys.f x 0) X₀ 1 1 fuel = some Rτ ∧
      ![1 / 2, 0] ∈ Rτ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ![1 / 2, 0] ∉ sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U
          t := by -- --- PROOF ---
  intro sys X₀
  let A : Mat ℝ 2 2 := !![0, 1; 0, 0]
  replace hcen : ops.cen X₀ = 0 := hcen
  replace hbox : X₀ ⊆ ops.box X₀ := hbox
  replace hjac : ∀ x, ops.jac x = A := hjac
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hf0 : sys.f 0 0 = 0 := by
    ext i; fin_cases i <;> rfl
  have hmd : ∀ T : Set (Vec ℝ 2), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  -- the subroutines' values: `C = {0}` (17), `L = 0` (9), `R̂_err(0) = {0}` (13), `μ0 = 0`
  have hB : (ops.box X₀).Nonempty :=
    (nonempty_Icc.mpr fun i => by fin_cases i <;> norm_num).mono hbox
  have hC : ops.curv 1 A (ops.box X₀) 0 = {0} := by
    rw [hcurv]; exact NonlinearSys.innerCurvatureError_shear 1 hη hB
  have hL : ∀ x D, ops.lagr x D = {0} := fun x D => by
    rw [hlagr]; exact NonlinearSys.innerLagrangeRemainder_shear x D
  have hE : ops.err 1 A {0} = {0} := by rw [herr]; exact NonlinearSys.innerAbstrErr_shear 1 hη
  have hs : ops.smul (11 / 10) {0} = {0} := by rw [hsmul, Set.smul_set_singleton, smul_zero]
  have hss : ops.sub {0} {0} = true := (hsub _ _).mpr subset_rfl
  -- `e^{A} = I + A`, as `A² = 0`
  have hexp : exp ((1 : ℝ) • A) = 1 + A := by rw [NonlinearSys.exp_smul_shear, one_smul]
  -- what one step computes
  have hrun : NonlinearSys.innerMinkDiff ops (fun x => sys.f x 0) X₀ 1 1 (k + 1) =
      some (∅ ∪ convexHull ℝ (X₀ ∪ (fun x => exp ((1 : ℝ) • A) *ᵥ x) '' X₀)) := by
    simp [NonlinearSys.innerMinkDiff, NonlinearSys.innerMinkDiffLoop,
      NonlinearSys.innerMinkDiffStep, NonlinearSys.innerMinkDiffRemainder, hcen, hf0, hjac, hC,
      hzero, hs, hE, hL, hss, hcen0, hmd]
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
    -- the field `(x₂, 0)` is continuous along the run, so the run is classical
    have hcont : ContinuousOn (fun s => sys.f (x s) (u s)) (Icc 0 t) := by
      refine continuousOn_pi.mpr fun i => ?_
      fin_cases i
      · exact (continuous_apply 1).comp_continuousOn traj.cont
      · exact continuousOn_const
    have hder : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt x ![x s 1, 0] (Icc 0 t) s :=
      fun s hs => traj.hasDerivWithinAt ⟨le_rfl, ht.1⟩ hcont hs
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
