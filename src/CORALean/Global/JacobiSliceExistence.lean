module

public import CORALean.Global.JacobiExistence
public import CORALean.Global.JacobiSlice

@[expose] public section

/-!
# The preconditioned Jacobi test on a slice proves a pre-image

`f : ℝᵐ → ℝⁿ` is `C¹` with Jacobian `Df`, `C` is injective, `ind` picks `n` coordinates, and
`v ↦ jacobiSlice xc ind v` holds the others at `xc`. If the interval matrix `[Jlo, Jhi]` encloses
the picked columns of `C Df` on the slice of the box `[lo, hi]`, and every Jacobi step for
`C f(slice v) = C y` lands in the box, then `y = f(slice v)` for some `v` in the box. This is the
square test `exists_mem_Icc_eq_add_of_jacobi` for `F(v) = C f(slice v)`, whose Jacobian is the
picked columns of `C Df`, followed by the injectivity of `C`. At `m = n` and `ind` the identity it
is [1, Cor. 2.1] with the closed inclusion and a preconditioner; for `m > n` it is [1, Cor. 3.1]
on the slice at `ũ₂`, the argument of `Icc_subset_image_of_innerTest_closed`.

## Inputs
* `f` – smooth map
* `Df` – its Jacobian matrix
* `xc` – base point
* `ind` – indices of the selected coordinates
* `C` – preconditioning matrix
* `lo` – lower end of the slice box
* `hi` – upper end of the slice box
* `Jlo` – lower end of the Jacobian enclosure
* `Jhi` – upper end of the Jacobian enclosure
* `y` – target value

## Hypotheses
* `hf` – the map is continuously differentiable
* `hDf` – the matrix is its derivative everywhere
* `hC` – the preconditioner is injective
* `hxc` – the base point's selected coordinates lie in the box
* `hJ` – the enclosure contains the preconditioned columns on the slice
* `hstep` – every Jacobi step for a matrix in the enclosure lands in the box

## Conclusion
* some point of the box has its slice image equal to the target

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

open Set Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- At the selected coordinates of `xc` itself, the slice is `xc`. -/
theorem aux_jacobiSlice_self (xc : Fin m → ℝ) (ind : Fin n → Fin m) :
    jacobiSlice xc ind (fun i => xc (ind i)) = xc := by
  simp [jacobiSlice]


/-- The selection matrix of `ind` applied to a unit vector is the unit vector at `ind j`. -/
theorem aux_select_mulVec_single {ind : Fin n → Fin m} (j : Fin n) : -- --- CONCL ---
    (Matrix.of fun k i => if ind i = k then (1 : ℝ) else 0) *ᵥ Pi.single j 1
      = Pi.single (ind j) 1 := by -- --- PROOF ---
  funext k
  simp only [mulVec, dotProduct, of_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j (fun i _ hi => if_neg hi) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [if_true]
  by_cases h : ind j = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.1] on the slice, preconditioned, with the closed inclusion. -/
theorem exists_jacobiSlice_eq_of_jacobi {f : (Fin m → ℝ) → (Fin n → ℝ)} (hf : ContDiff ℝ 1 f)
    {Df : (Fin m → ℝ) → Matrix (Fin n) (Fin m) ℝ}
    (hDf : ∀ z, HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' (Df z))) z)
    (xc : Fin m → ℝ) {ind : Fin n → Fin m}
    {C : Matrix (Fin n) (Fin n) ℝ} (hC : Function.Injective C.mulVec) {lo hi : Fin n → ℝ}
    (hxc : (fun i => xc (ind i)) ∈ Icc lo hi) {Jlo Jhi : Fin n → Fin n → ℝ}
    (hJ : ∀ v ∈ Icc lo hi, ∀ i j,
      (C * Df (jacobiSlice xc ind v)) i (ind j) ∈ Icc (Jlo i j) (Jhi i j))
    (y : Fin n → ℝ)
    (hstep : ∀ A : Fin n → Fin n → ℝ, (∀ i j, A i j ∈ Icc (Jlo i j) (Jhi i j)) →
      ∀ v ∈ Icc lo hi, ∀ i, A i i ≠ 0 ∧
        xc (ind i) + ((C *ᵥ (y - f xc)) i
          - ∑ j ∈ Finset.univ.erase i, A i j * (v j - xc (ind j))) / A i i ∈ Icc (lo i) (hi i))
    : -- --- CONCL ---
    ∃ v ∈ Icc lo hi, f (jacobiSlice xc ind v) = y := by -- --- PROOF ---
  set P : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun k i => if ind i = k then (1 : ℝ) else 0
  set F : (Fin n → ℝ) → (Fin n → ℝ) := fun v => C *ᵥ f (jacobiSlice xc ind v)
  -- the slice is affine with linear part `P`
  have hS : ∀ v, HasFDerivAt (jacobiSlice xc ind)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' P)) v := fun v => by
    have h := ((LinearMap.toContinuousLinearMap (Matrix.toLin' P)).hasFDerivAt.comp v
      ((hasFDerivAt_id v).sub_const (fun i => xc (ind i)))).const_add xc
    simpa [jacobiSlice, Function.comp_def, P] using h
  have hSc : ContDiff ℝ 1 (jacobiSlice xc ind) :=
    contDiff_const.add ((LinearMap.toContinuousLinearMap (Matrix.toLin' P)).contDiff.comp
      (contDiff_id.sub contDiff_const))
  have hF : ContDiff ℝ 1 F :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).contDiff.comp (hf.comp hSc)
  -- the derivative of `F` along `e_j` is column `ind j` of `C Df`
  have hFd : ∀ v (i j : Fin n),
      fderiv ℝ F v (Pi.single j 1) i = (C * Df (jacobiSlice xc ind v)) i (ind j) := by
    intro v i j
    have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).hasFDerivAt.comp v
      ((hDf (jacobiSlice xc ind v)).comp v (hS v))
    rw [show F = (LinearMap.toContinuousLinearMap (Matrix.toLin' C)) ∘ f ∘ jacobiSlice xc ind
      from rfl, h.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
    rw [aux_select_mulVec_single, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  -- the square test for `F` at `xc ∘ ind`, whose slice is `xc`
  obtain ⟨v, hv, hFv⟩ := exists_mem_Icc_eq_add_of_jacobi hF hxc (Jlo := Jlo) (Jhi := Jhi)
    (fun v hv i j => by rw [hFd]; exact hJ v hv i j) (C *ᵥ (y - f xc)) hstep
  refine ⟨v, hv, hC ?_⟩
  have e : F (fun i => xc (ind i)) = C *ᵥ f xc := by simp only [F, aux_jacobiSlice_self]
  rw [e, ← Matrix.mulVec_add, add_sub_cancel] at hFv
  exact hFv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
