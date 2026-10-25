module

public import CORALean.Global.Brouwer
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# The interval Jacobi test proves a zero, with a closed inclusion

`F : ℝⁿ → ℝⁿ` is `C¹`, its partial derivatives on the box `x = [lo, hi]` lie in the interval matrix
`[Jlo, Jhi]`, `x̃ ∈ x`, and every value of the Jacobi step `x̃ᵢ + (bᵢ - Σ_{j≠i} Aᵢⱼ (xⱼ - x̃ⱼ)) /
Aᵢᵢ`, over the real `A` in the interval matrix and the `x` in the box, lies in `[loᵢ, hiᵢ]`. Then `F
x = F x̃ + b` has a solution in the box: [1, Cor. 2.1]'s test with `⊆ x` in place of `⊆ int(x)`, as
CORA's `aux_InnerSpecial` checks it. The average Jacobian `A(x)` is continuous, in the interval
matrix, with `F x - F x̃ = A(x)(x - x̃)`, so the Jacobi map with `A(x)` is a continuous self-map of
the box; Brouwer's theorem (`exists_fixedPoint_of_isCompact_convex`) fixes a point, where `A(x)(x -
x̃) = b`.

## Inputs
* `F` – continuously differentiable map
* `lo` – lower end of the box
* `hi` – upper end of the box
* `xc` – expansion point
* `Jlo` – lower end of the Jacobian enclosure
* `Jhi` – upper end of the Jacobian enclosure
* `b` – right-hand side

## Hypotheses
* `hF` – the map is continuously differentiable
* `hxc` – the expansion point lies in the box
* `hJ` – the enclosure contains the derivative on the box
* `hstep` – every Jacobi step for a matrix in the enclosure lands in the box

## Conclusion
* the equation has a solution in the box

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `(i, j)` partial derivative of `F` at `p`. -/
noncomputable def aux_pd (F : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) (i j : Fin n) : ℝ :=
  fderiv ℝ F p (Pi.single j 1) i

/-- Partial derivatives of a `C¹` map are continuous. -/
theorem aux_pd_continuous {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : ContDiff ℝ 1 F) (i j : Fin n) :
    Continuous fun p => aux_pd F p i j :=
  (continuous_apply i).comp ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)

/-- A derivative applied to `w`, entry by entry. -/
theorem aux_fderiv_apply_eq_sum (F : (Fin n → ℝ) → (Fin n → ℝ)) (p w : Fin n → ℝ)
    (i : Fin n) : -- --- CONCL ---
    fderiv ℝ F p w i = ∑ j, aux_pd F p i j * w j := by -- --- PROOF ---
  have h := LinearMap.pi_apply_eq_sum_univ (fderiv ℝ F p : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) w
  change (fderiv ℝ F p : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) w i = _
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (fun k => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k; simp [Pi.single_apply, eq_comm]
  simp [aux_pd, mul_comm, hj]

/-- The mean-value slope: `F x - F xc = A x (x - xc)` for `A x` the average Jacobian on the
segment. -/
theorem aux_sub_eq_sum {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : ContDiff ℝ 1 F) (c x : Fin n → ℝ)
    (i : Fin n) : -- --- CONCL ---
    F x i - F c i =
      ∑ j, (∫ s in (0 : ℝ)..1, aux_pd F (c + s • (x - c)) i j) * (x j - c j) := by -- --- PROOF ---
  set γ : ℝ → (Fin n → ℝ) := fun s => c + s • (x - c)
  have hγ : ∀ s, HasDerivAt γ (x - c) s := fun s => by
    have h := ((hasDerivAt_id s).smul_const (x - c)).const_add c
    simp only [id, one_smul] at h
    exact h
  have hder : ∀ s, HasDerivAt (fun s => F (γ s) i) (fderiv ℝ F (γ s) (x - c) i) s := fun s =>
    hasDerivAt_pi.mp
      (((hF.differentiable one_ne_zero) (γ s)).hasFDerivAt.comp_hasDerivAt s (hγ s)) i
  have hpc : ∀ j, Continuous fun s : ℝ => aux_pd F (c + s • (x - c)) i j * (x - c) j :=
    fun j => ((aux_pd_continuous hF i j).comp (by fun_prop)).mul continuous_const
  have hcont : Continuous fun s => fderiv ℝ F (γ s) (x - c) i := by
    simp only [aux_fderiv_apply_eq_sum]
    exact continuous_finsetSum _ fun j _ => hpc j
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s _ => hder s) (hcont.intervalIntegrable 0 1)
  simp only [γ, one_smul, zero_smul, add_zero, add_sub_cancel] at hftc
  rw [← hftc]
  simp only [aux_fderiv_apply_eq_sum]
  rw [intervalIntegral.integral_finsetSum fun j _ => (hpc j).intervalIntegrable 0 1]
  exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_mul_const _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 2.1] with a closed inclusion: if every Jacobi step lands in the box `[lo, hi]`, then
`F x = F xc + b` for some `x` in the box. -/
theorem exists_mem_Icc_eq_add_of_jacobi {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF : ContDiff ℝ 1 F)
    {lo hi xc : Fin n → ℝ} (hxc : xc ∈ Icc lo hi) {Jlo Jhi : Fin n → Fin n → ℝ}
    (hJ : ∀ x ∈ Icc lo hi, ∀ i j, fderiv ℝ F x (Pi.single j 1) i ∈
      Icc (Jlo i j) (Jhi i j)) (b : Fin n → ℝ)
    (hstep : ∀ A : Fin n → Fin n → ℝ, (∀ i j, A i j ∈ Icc (Jlo i j) (Jhi i j)) →
      ∀ x ∈ Icc lo hi, ∀ i, A i i ≠ 0 ∧
        xc i + (b i - ∑ j ∈ Finset.univ.erase i, A i j * (x j - xc j)) / A i i ∈
          Icc (lo i) (hi i)) : -- --- CONCL ---
    ∃ x ∈ Icc lo hi, F x = F xc + b := by -- --- PROOF ---
  set X := Icc lo hi
  set A : (Fin n → ℝ) → Fin n → Fin n → ℝ :=
    fun x i j => ∫ s in (0 : ℝ)..1, aux_pd F (xc + s • (x - xc)) i j
  -- the slope matrix is continuous and, on the box, inside the interval Jacobian
  have hAc : ∀ i j, Continuous fun x => A x i j := fun i j =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous fun q : (Fin n → ℝ) × ℝ => aux_pd F (xc + q.2 • (q.1 - xc)) i j from
        (aux_pd_continuous hF i j).comp (by fun_prop)) 0 1
  have hAJ : ∀ x ∈ X, ∀ i j, A x i j ∈ Icc (Jlo i j) (Jhi i j) := by
    intro x hx i j
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, xc + s • (x - xc) ∈ X := fun s hs =>
      (convex_Icc lo hi).add_smul_sub_mem hxc hx hs
    have hint : IntervalIntegrable (fun s => aux_pd F (xc + s • (x - xc)) i j)
        MeasureTheory.volume 0 1 :=
      ((aux_pd_continuous hF i j).comp (by fun_prop)).intervalIntegrable 0 1
    constructor
    · have := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hint
        fun s hs => (hJ _ (hseg s hs) i j).1
      simpa using this
    · have := intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
        fun s hs => (hJ _ (hseg s hs) i j).2
      simpa using this
  -- the Jacobi map, a self-map of the box
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x i =>
    xc i + (b i - ∑ j ∈ Finset.univ.erase i, A x i j * (x j - xc j)) / A x i i
  have hgc : ContinuousOn g X := by
    refine continuousOn_pi.mpr fun i => ?_
    refine continuousOn_const.add (ContinuousOn.div ?_ (hAc i i).continuousOn
      fun x hx => (hstep (A x) (hAJ x hx) x hx i).1)
    exact (continuousOn_const.sub (continuousOn_finsetSum _ fun j _ =>
      ((hAc i j).continuousOn).mul ((continuous_apply j).continuousOn.sub continuousOn_const)))
  have hgX : MapsTo g X X := fun x hx =>
    ⟨fun i => (hstep (A x) (hAJ x hx) x hx i).2.1, fun i => (hstep (A x) (hAJ x hx) x hx i).2.2⟩
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_of_isCompact_convex isCompact_Icc (convex_Icc lo hi)
    ⟨xc, hxc⟩ hgc hgX
  -- at the fixed point each row of `A x (x - xc) = b` holds, and that is `F x - F xc`
  refine ⟨x, hx, funext fun i => ?_⟩
  have hi := congrFun hfix i
  have hne := (hstep (A x) (hAJ x hx) x hx i).1
  simp only [g] at hi
  have hrow : ∑ j, A x i j * (x j - xc j) = b i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    field_simp at hi
    linarith
  have := aux_sub_eq_sum hF xc x i
  simp only [Pi.add_apply]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
