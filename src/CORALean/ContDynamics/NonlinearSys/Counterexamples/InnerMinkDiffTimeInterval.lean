module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiff
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import CORALean.Specification.STL.Operations.DepCurvatureF
public import CORALean.Specification.STL.Operations.DepCurvatureG
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
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
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
  Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 71(1):352-367,
  2026.
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

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- (17): the curvature error `C = F box(X₀) ⊕ G w` at the shifted box `B`, `F`, `G` of
[2, (19), (28)] (its authors' version; [1] cites arXiv v2, which numbers (19), (20), (28) as
(18), (19), (26)). -/
noncomputable def NonlinearSys.aux_curvature (η : ℕ) (Δt : ℝ) (A : Mat ℝ n n)
    (B : Set (Vec ℝ n)) (w : Vec ℝ n) : Set (Vec ℝ n) :=
  -- [2, (19)] F
  let F := STL.depCurvatureF A Δt η
  -- [2, (28)] G
  let G := STL.depCurvatureG A Δt η
  -- (17) C = F box(X₀) ⊕ G w
  (⋃ M ∈ F.construct, (fun x => M *ᵥ x) '' B) + ⋃ N ∈ G.construct, {N *ᵥ w}

/-- (13): the abstraction error `R̂_err(L) = ⊕_{j=0}^η A^jΔt^{j+1}/(j+1)! L ⊕ E(Δt)ΔtL`, `E` the
remainder of [2, (20)]. -/
noncomputable def NonlinearSys.aux_abstrErr (η : ℕ) (Δt : ℝ) (A : Mat ℝ n n)
    (L : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  -- [2, (20)] E = [-E(Δt,η), E(Δt,η)]
  let E := Real.MatExp.expRemainderInterval A Δt η
  -- (13) ⊕_{j=0}^η A^j Δt^{j+1}/(j+1)! L ⊕ E(Δt) Δt L
  (∑ j ∈ Finset.range (η + 1), (fun l => ((Δt ^ (j + 1) / (j + 1).factorial) • A ^ j) *ᵥ l) '' L)
    + ⋃ M ∈ E, (fun l => (Δt • M) *ᵥ l) '' L

/-- (9): the Lagrange remainder of `f` at `x*` over `X`, `[-l̂, l̂]` with
`l̂⁽ⁱ⁾ = ½ max|x - x*|ᵀ max D²f⁽ⁱ⁾ max|x - x*|`. -/
noncomputable def NonlinearSys.aux_lagrangeRemainder (f : Vec ℝ n → Vec ℝ n) (xstar : Vec ℝ n)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  -- (9) max_{x∈X} |x - x*|
  let γ : Vec ℝ n := fun j => ⨆ x ∈ X, |x j - xstar j|
  -- (9) max_{ζ∈X} D²f⁽ⁱ⁾(ζ)
  let H : Fin n → Mat ℝ n n := fun i j k =>
    ⨆ ζ ∈ X, |fderiv ℝ (fderiv ℝ f) ζ (Pi.single j 1) (Pi.single k 1) i|
  -- (9) l̂⁽ⁱ⁾ = ½ γᵀ H⁽ⁱ⁾ γ
  let l : Vec ℝ n := fun i => γ ⬝ᵥ (H i *ᵥ γ) / 2
  -- (9) L̂ = [-l̂, l̂]
  Icc (-l) l

/-- `A⁽ⁱ⁾ = 0` for `i ≥ 2`. -/
theorem NonlinearSys.aux_shear_pow {i : ℕ} (hi : 2 ≤ i) : (!![0, 1; 0, 0] : Mat ℝ 2 2) ^ i = 0 :=
  pow_eq_zero_of_le hi (by
    ext j k; fin_cases j <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two])

/-- `e^{AΔt} = I + AΔt`. -/
theorem NonlinearSys.aux_shear_exp (Δt : ℝ) : -- --- CONCL ---
    exp (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) = 1 + Δt • !![0, 1; 0, 0] := by -- --- PROOF ---
  rw [exp_eq_tsum ℝ]
  show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) ^ i = _
  rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
    rw [smul_pow, NonlinearSys.aux_shear_pow (by simp at hb; omega), smul_zero, smul_zero]]
  simp [Finset.sum_range_succ]

/-- [2, (20)]: `E(Δt, η) = e^{|A|Δt} - Σ_{i≤η} (|A|Δt)ⁱ/i! = 0` for `η ≥ 1`, as `|A| = A`. -/
theorem NonlinearSys.aux_shear_expRemainderMat (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    Real.MatExp.expRemainderMat !![0, 1; 0, 0] Δt η = 0 := by -- --- PROOF ---
  have habs : Real.MatExp.absMat (!![0, 1; 0, 0] : Mat ℝ 2 2) = !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Real.MatExp.absMat]
  have htay : Real.MatExp.expTaylor (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) η =
      1 + Δt • !![0, 1; 0, 0] := by
    obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
    rw [Real.MatExp.expTaylor, Finset.sum_range_succ', Finset.sum_range_succ',
      Finset.sum_eq_zero fun i _ => by
        rw [smul_pow, NonlinearSys.aux_shear_pow (by omega), smul_zero, smul_zero]]
    simp [add_comm]
  rw [Real.MatExp.expRemainderMat, habs, NonlinearSys.aux_shear_exp, htay, sub_self]

/-- [2, (19)]: `F = ⊕_{i=2}^η […] Aⁱ/i! ⊕ E = {0}` for `η ≥ 1`. -/
theorem NonlinearSys.aux_shear_depCurvatureF (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    (STL.depCurvatureF !![0, 1; 0, 0] Δt η).construct = {0} := by -- --- PROOF ---
  have hT : ∀ i j k, Real.MatExp.corrTerm !![0, 1; 0, 0] Δt (i + 2) j k = 0 := fun i j k => by
    simp [Real.MatExp.corrTerm, NonlinearSys.aux_shear_pow (i := i + 2) (by omega)]
  ext M
  simp only [Real.Interval.construct, STL.depCurvatureF, hT,
    NonlinearSys.aux_shear_expRemainderMat Δt hη, min_self, max_self, Finset.sum_const_zero,
    Matrix.zero_apply, sub_zero, add_zero, mem_setOf_eq, mem_singleton_iff, Entrywise.entry_mat]
  constructor
  · intro h; ext j k; exact le_antisymm (h (j, k)).2 (h (j, k)).1
  · rintro rfl p; simp

/-- (17): `C = F box(X₀) ⊕ G w = {0}` for `η ≥ 1`, `w = 0` and a nonempty box, though `G ≠ 0`. -/
theorem NonlinearSys.aux_shear_curvature (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) {B : Set (Vec ℝ 2)}
    (hB : B.Nonempty) : -- --- CONCL ---
    NonlinearSys.aux_curvature η Δt !![0, 1; 0, 0] B 0 = {0} := by -- --- PROOF ---
  have hG : (0 : Mat ℝ 2 2) ∈ (STL.depCurvatureG !![0, 1; 0, 0] Δt η).construct := fun p => by
    simp only [STL.depCurvatureG, NonlinearSys.aux_shear_expRemainderMat Δt hη,
      Entrywise.entry_mat, Matrix.zero_apply, mul_zero, sub_zero, add_zero]
    exact ⟨Finset.sum_nonpos fun _ _ => min_le_right _ _,
      Finset.sum_nonneg fun _ _ => le_max_right _ _⟩
  have h1 : (⋃ M ∈ (STL.depCurvatureF !![0, 1; 0, 0] Δt η).construct,
      (fun x => M *ᵥ x) '' B) = {0} := by
    rw [NonlinearSys.aux_shear_depCurvatureF Δt hη]; simp [hB.image_const]
  have h2 : (⋃ N ∈ (STL.depCurvatureG !![0, 1; 0, 0] Δt η).construct,
      ({N *ᵥ (0 : Vec ℝ 2)} : Set _)) = {0} := by
    simp only [Matrix.mulVec_zero]
    exact Set.biUnion_const ⟨0, hG⟩ _
  simp only [NonlinearSys.aux_curvature, h1, h2, Set.singleton_add_singleton, add_zero]

/-- (13): `R̂_err(0) = {0}` for `η ≥ 1`. -/
theorem NonlinearSys.aux_shear_abstrErr (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    NonlinearSys.aux_abstrErr η Δt !![0, 1; 0, 0] {0} = {0} := by -- --- PROOF ---
  have h0 : (0 : Mat ℝ 2 2) ∈ Real.MatExp.expRemainderInterval !![0, 1; 0, 0] Δt η :=
    fun j k => by simp [NonlinearSys.aux_shear_expRemainderMat Δt hη]
  have h1 : ∀ M : Mat ℝ 2 2, (fun l => M *ᵥ l) '' ({0} : Set (Vec ℝ 2)) = 0 := fun M => by
    rw [Set.image_singleton, Matrix.mulVec_zero, Set.singleton_zero]
  simp only [NonlinearSys.aux_abstrErr, h1, Finset.sum_const_zero, zero_add]
  rw [← Set.singleton_zero]
  exact Set.biUnion_const ⟨0, h0⟩ _

/-- (9): `L = [0, 0]` for the linear `f(x) = (x₂, 0)`, as `D²f ≡ 0`. -/
theorem NonlinearSys.aux_shear_lagrangeRemainder (xstar : Vec ℝ 2)
    (X : Set (Vec ℝ 2)) : -- --- CONCL ---
    NonlinearSys.aux_lagrangeRemainder (fun x : Vec ℝ 2 => (![x 1, 0] : Vec ℝ 2)) xstar X =
      {0} := by -- --- PROOF ---
  let L : Vec ℝ 2 →L[ℝ] Vec ℝ 2 := LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 1; 0, 0])
  have hf : (fun x : Vec ℝ 2 => (![x 1, 0] : Vec ℝ 2)) = ⇑L := by
    funext y; ext i; fin_cases i <;> simp [L, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hD : fderiv ℝ (fderiv ℝ ⇑L) = 0 := by
    rw [show fderiv ℝ ⇑L = fun _ => L from funext fun _ => L.fderiv]
    funext y; exact fderiv_const_apply L
  simp only [NonlinearSys.aux_lagrangeRemainder, hf, hD, Pi.zero_apply, _root_.zero_apply,
    abs_zero, Real.iSup_const_zero]
  have hl : (fun i : Fin 2 => (fun j => ⨆ y ∈ X, |y j - xstar j|) ⬝ᵥ
      ((fun _ _ => (0 : ℝ)) *ᵥ fun j => ⨆ y ∈ X, |y j - xstar j|) / 2) = 0 := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hl, neg_zero, Set.Icc_self]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s output `R̂(τ)` for the shear `ẋ = (x₂, 0)` from `[-1/10, 1/10] × [-1, 1]` over
`[0, 1]` in one step, at any Taylor order `η ≥ 1`, holds `(1/2, 0)`, which no run reaches at any
`t ∈ [0, 1]`; `curv`, `err` and `lagr` are (17), (13) and (9), their values derived. -/
theorem NonlinearSys.innerMinkDiff_timeInterval_counterexample
    (ops : NonlinearSys.InnerMinkDiffOps 2 (Set (Vec ℝ 2))) (η : ℕ) (hη : 1 ≤ η) (fuel : ℕ)
    (hfuel : 0 < fuel) (U : Set (Vec ℝ 1))
    (hcen : ops.cen (Icc ![-1 / 10, -1] ![1 / 10, 1]) = 0) (hcen0 : ops.cen {0} = 0)
    (hbox : Icc ![-1 / 10, -1] ![1 / 10, 1] ⊆ ops.box (Icc ![-1 / 10, -1] ![1 / 10, 1]))
    (hjac : ∀ x, ops.jac x = !![0, 1; 0, 0]) (hcurv : ops.curv = NonlinearSys.aux_curvature η)
    (herr : ops.err = NonlinearSys.aux_abstrErr η)
    (hlagr : ops.lagr = NonlinearSys.aux_lagrangeRemainder fun x => ![x 1, 0])
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
    rw [hcurv]; exact NonlinearSys.aux_shear_curvature 1 hη hB
  have hL : ∀ x D, ops.lagr x D = {0} := fun x D => by
    rw [hlagr]; exact NonlinearSys.aux_shear_lagrangeRemainder x D
  have hE : ops.err 1 A {0} = {0} := by rw [herr]; exact NonlinearSys.aux_shear_abstrErr 1 hη
  have hs : ops.smul (11 / 10) {0} = {0} := by rw [hsmul, Set.smul_set_singleton, smul_zero]
  have hss : ops.sub {0} {0} = true := (hsub _ _).mpr subset_rfl
  -- `e^{A} = I + A`, as `A² = 0`
  have hexp : exp ((1 : ℝ) • A) = 1 + A := by rw [NonlinearSys.aux_shear_exp, one_smul]
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
