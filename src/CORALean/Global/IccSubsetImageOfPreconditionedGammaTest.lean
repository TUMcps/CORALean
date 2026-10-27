module

public import CORALean.Global.IccSubsetImageOfGammaTest
public import CORALean.Global.SubsetImageOfPreconditioned
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# The preconditioned inclusion test proves a box inside the range

[1, Eq. 4]: for a regular real matrix `C`, the inclusion (2) of the corollary (`PassesGammaTest`)
for `C f` with the interval Jacobian `C J` and the box `C y` gives `y ⊆ range(f, x)`. Here
`z = [zlo, zhi]` is the box `C y` (any box holding `C y` for the `y ∈ y`, which the interval product
computes), and `[Jlo, Jhi]` encloses `C f'` on `int x`, the interval Jacobian `C J` of `C f`.
The proof is the paper's: the corollary for `C f` puts `z` in the range of `C f`
(`Icc_subset_image_of_gammaTest`), and (3) (`subset_image_of_preconditioned_subset`) takes
`C y ⊆ z` back to `y ⊆ range(f, x)`.

## Inputs
* `f` – map
* `f'` – its derivative
* `x₀` – expansion point
* `xlo` – lower end of the domain box
* `xhi` – upper end of the domain box
* `ylo` – lower end of the target box
* `yhi` – upper end of the target box
* `zlo` – lower end of the preconditioned box
* `zhi` – upper end of the preconditioned box
* `Jlo` – lower end of the Jacobian enclosure
* `Jhi` – upper end of the Jacobian enclosure
* `C` – preconditioning matrix

## Hypotheses
* `hC` – the preconditioner is regular
* `hf` – the derivative is strict at interior points
* `hcont` – the map is continuous on the domain box
* `hJ₁` – the Jacobian enclosure contains the preconditioned derivative at interior points
* `hJ` – the enclosure's ends are ordered
* `hdiag` – no diagonal enclosure contains zero
* `hx₀` – the expansion point lies in the domain box
* `hz` – the preconditioner maps the target box into the preconditioned box
* `hy` – the map's value at the expansion point lies in the target box
* `h4` – the preconditioned inclusion test holds

## Conclusion
* the target box lies in the image of the domain box

## References

* [1] [A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued functions".
      Reliable Computing, 2010.](../../../references/2010/goldsztejn-rc-inner-range.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 4]: the preconditioned inclusion gives `y ⊆ f(x)`, for `det C ≠ 0`. -/
theorem Icc_subset_image_of_preconditioned_gammaTest
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {x₀ xlo xhi ylo yhi zlo zhi : Fin n → ℝ} {Jlo Jhi : Matrix (Fin n) (Fin n) ℝ}
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (hf : ∀ x ∈ interior (Icc xlo xhi), HasStrictFDerivAt f (f' x) x)
    (hcont : ContinuousOn f (Icc xlo xhi))
    (hJ₁ : ∀ x ∈ interior (Icc xlo xhi), ∀ i j,
      (C *ᵥ fun k => f' x (Pi.single j 1) k) i ∈ Icc (Jlo i j) (Jhi i j))
    (hJ : ∀ i j, Jlo i j ≤ Jhi i j) (hdiag : ∀ i, (0 : ℝ) ∉ Icc (Jlo i i) (Jhi i i))
    (hx₀ : x₀ ∈ Icc xlo xhi) (hz : ∀ y ∈ Icc ylo yhi, C *ᵥ y ∈ Icc zlo zhi)
    (hy : f x₀ ∈ Icc ylo yhi)
    (h4 : PassesGammaTest (fun x => C *ᵥ f x) x₀ xlo xhi Jlo Jhi zlo zhi) : -- --- CONCL ---
    Icc ylo yhi ⊆ f '' Icc xlo xhi := by -- --- PROOF ---
  -- `C f` is differentiable with derivative `C f'`
  let A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' C)
  have hA : ∀ w, A w = C *ᵥ w := fun w => by simp [A]
  have hg : ∀ x ∈ interior (Icc xlo xhi),
      HasStrictFDerivAt (fun x => C *ᵥ f x) (A.comp (f' x)) x := fun x hx => by
    have hfun : (fun x => C *ᵥ f x) = A ∘ f := funext fun x => (hA _).symm
    rw [hfun]
    exact A.hasStrictFDerivAt.comp x (hf x hx)
  have hgc : ContinuousOn (fun x => C *ᵥ f x) (Icc xlo xhi) :=
    A.continuous.comp_continuousOn hcont |>.congr fun x _ => hA _
  have hzr := Icc_subset_image_of_gammaTest hg hgc
    (fun x hx i j => by simpa only [ContinuousLinearMap.comp_apply, hA] using hJ₁ x hx i j)
    hJ hdiag hx₀ (hz _ hy) h4
  exact subset_image_of_preconditioned_subset C hC fun w ⟨y, hyy, hw⟩ => hw ▸ hzr (hz y hyy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
