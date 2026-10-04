import CORALean.Global.InnerRangeTest
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The preconditioned inclusion test

[1, Eq. 10]: the test of [1, Cor. 3.1] run on `C f₁:ᵣ` with the box `C y₁`,
`H_{f₁:ᵣ}(C J_{f₁:ᵣ}, ũ, u, C y₁) ⊆ int(u₁)`. The `C` that works is `r × r`: the paper takes
the first `r` columns of `D_ũ⁻¹`, an `m × r` matrix whose product with the `r × m` Jacobian
is `m × m`, and names the blocks `(C₁, C₂)` without using them. Its upper block `C₁` is
`J₁(ũ)⁻¹`, the lower one `0`; that `C₁` is the preconditioner here, and CORA's
`aux_preconditionMatrix` takes it too. Soundness needs only `det C ≠ 0`: (5) for `C f₁:ᵣ`
puts the box `z ⊇ C y₁` in `C f₁:ᵣ(u)`, and `C` is injective.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix

variable {r s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 10]: the test on `C f₁:ᵣ`, `det C ≠ 0`, against a box `z ⊇ C y₁` gives
`y₁ ⊆ f₁:ᵣ(u)`. -/
theorem Icc_subset_image_of_preconditioned_innerTest
    {g : (Fin r → ℝ) × (Fin s → ℝ) → (Fin r → ℝ)}
    {g' : (Fin r → ℝ) × (Fin s → ℝ) → ((Fin r → ℝ) × (Fin s → ℝ) →L[ℝ] (Fin r → ℝ))}
    {ũ : (Fin r → ℝ) × (Fin s → ℝ)} {lo₁ hi₁ : Fin r → ℝ} {lo₂ hi₂ : Fin s → ℝ}
    {J₁lo J₁hi : Matrix (Fin r) (Fin r) ℝ} {J₂lo J₂hi : Matrix (Fin r) (Fin s) ℝ}
    {ylo yhi zlo zhi : Fin r → ℝ} (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.det ≠ 0)
    (hg : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, HasStrictFDerivAt g (g' x) x)
    (h3 : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂,
      (Matrix.of fun i j => g' x (Pi.single j 1, 0) i).det ≠ 0)
    (hJ₁ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i j,
      (C * Matrix.of fun i j => g' x (Pi.single j 1, 0) i) i j ∈ Icc (J₁lo i j) (J₁hi i j))
    (hJ₂ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i l,
      (C * Matrix.of fun i l => g' x (0, Pi.single l 1) i) i l ∈ Icc (J₂lo i l) (J₂hi i l))
    (hdiag : ∀ i, (0 : ℝ) ∉ Icc (J₁lo i i) (J₁hi i i)) (hũ : ũ ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂)
    (hz : ∀ y ∈ Icc ylo yhi, C *ᵥ y ∈ Icc zlo zhi) (hii : g ũ ∈ Icc ylo yhi)
    (h10 : innerTest (fun x => C *ᵥ g x) ũ lo₁ hi₁ lo₂ hi₂ J₁lo J₁hi J₂lo J₂hi zlo zhi) :
    Icc ylo yhi ⊆ g '' (Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂) := by -- --- PROOF ---
  let L : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin C)
  -- the entries of `C g'(x)` are those of `C J(x)`
  have hent : ∀ x w i, (L.comp (g' x)) w i = ∑ k, C i k * g' x w k := fun x w i => rfl
  have hJ₁' : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i j,
      (L.comp (g' x)) (Pi.single j 1, 0) i ∈ Icc (J₁lo i j) (J₁hi i j) := fun x hx i j => by
    rw [hent]; exact hJ₁ x hx i j
  have hJ₂' : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i l,
      (L.comp (g' x)) (0, Pi.single l 1) i ∈ Icc (J₂lo i l) (J₂hi i l) := fun x hx i l => by
    rw [hent]; exact hJ₂ x hx i l
  have h3' : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂,
      (Matrix.of fun i j => (L.comp (g' x)) (Pi.single j 1, 0) i).det ≠ 0 := by
    intro x hx
    have heq : (Matrix.of fun i j => (L.comp (g' x)) (Pi.single j 1, 0) i)
        = C * Matrix.of fun i j => g' x (Pi.single j 1, 0) i := by
      ext i j; rw [Matrix.of_apply, hent]; rfl
    rw [heq, Matrix.det_mul]
    exact mul_ne_zero hC (h3 x hx)
  have hsub := Icc_subset_image_of_innerTest (g := fun x => C *ᵥ g x)
    (g' := fun x => L.comp (g' x)) (fun x hx => L.hasStrictFDerivAt.comp x (hg x hx)) h3' hJ₁'
    hJ₂' hdiag hũ (hz _ hii) h10
  -- `C` is injective, so `C y = C g(x)` gives `y = g(x)`
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC))
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hsub (hz y hy)
  exact ⟨x, hx, hinj hxy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
