import CORALean.Global.JacobiExistence

/-!
# The inclusion test for an inner box, with a closed inclusion

[1, Cor. 3.1]'s test (5), `H ⊆ int(u₁)`, as [1, Alg. 3] and CORA's `aux_InnerGeneral` check it:
`H ⊆ u₁`, the closed box. `H = ũ₁ + Diag⁻¹(J₁)(y₁ - f₁:ᵣ(ũ) - OffDiag(J₁)(u₁ - ũ₁) - J₂(u₂ - ũ₂))`
is read over real matrices `J₁, J₂` in the interval ones and points of `y₁` and `u`, which any
interval evaluation of `H` encloses. Then `y₁ ⊆ f₁:ᵣ(u)`.

`Icc_subset_image_of_innerTest` proves the open version through [1, Thm. 3.1]; the closed one
needs a fixed point instead. On the slice `v ↦ f₁:ᵣ(v, ũ₂)` the `J₂` term is `0`, so (5) there
is the Jacobi step of `exists_mem_Icc_eq_add_of_jacobi`, whose fixed point solves
`f₁:ᵣ(v, ũ₂) = y` for each `y ∈ y₁`. Neither (3) nor `f₁:ᵣ(ũ) ∈ y₁` is used; `f₁:ᵣ` is `C¹`.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {r s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.1] with `H ⊆ u₁` in place of `H ⊆ int(u₁)`: every `y ∈ y₁` is `f₁:ᵣ(v, ũ₂)` for
some `v ∈ u₁`. -/
theorem Icc_subset_image_of_innerTest_closed {g : (Fin r → ℝ) × (Fin s → ℝ) → (Fin r → ℝ)}
    (hg : ContDiff ℝ 1 g) {ũ : (Fin r → ℝ) × (Fin s → ℝ)} {lo₁ hi₁ : Fin r → ℝ}
    {lo₂ hi₂ : Fin s → ℝ} {J₁lo J₁hi : Matrix (Fin r) (Fin r) ℝ}
    {J₂lo J₂hi : Matrix (Fin r) (Fin s) ℝ} {ylo yhi : Fin r → ℝ}
    (hJ₁ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i j,
      fderiv ℝ g x (Pi.single j 1, 0) i ∈ Icc (J₁lo i j) (J₁hi i j))
    (hJ₂ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i l,
      fderiv ℝ g x (0, Pi.single l 1) i ∈ Icc (J₂lo i l) (J₂hi i l))
    (hdiag : ∀ i, (0 : ℝ) ∉ Icc (J₁lo i i) (J₁hi i i)) (hũ : ũ ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂)
    (h5 : ∀ y ∈ Icc ylo yhi, ∀ J₁ : Matrix (Fin r) (Fin r) ℝ,
      (∀ i j, J₁ i j ∈ Icc (J₁lo i j) (J₁hi i j)) →
      ∀ J₂ : Matrix (Fin r) (Fin s) ℝ, (∀ i l, J₂ i l ∈ Icc (J₂lo i l) (J₂hi i l)) →
      ∀ v ∈ Icc lo₁ hi₁, ∀ w ∈ Icc lo₂ hi₂, ∀ i,
        ũ.1 i + (y i - g ũ i - ∑ j ∈ Finset.univ.erase i, J₁ i j * (v j - ũ.1 j)
          - ∑ l, J₂ i l * (w l - ũ.2 l)) / J₁ i i ∈ Icc (lo₁ i) (hi₁ i)) :
    Icc ylo yhi ⊆ g '' (Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂) := by -- --- PROOF ---
  intro y hy
  -- the slice `F(v) = g(v, ũ₂)` and its partial derivatives
  set F : (Fin r → ℝ) → (Fin r → ℝ) := fun v => g (v, ũ.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_id.prodMk contDiff_const)
  have hF' : ∀ v w, fderiv ℝ F v w = fderiv ℝ g (v, ũ.2) (w, 0) := fun v w => by
    have hin : HasFDerivAt (fun x : Fin r → ℝ => (x, ũ.2))
        ((ContinuousLinearMap.id ℝ (Fin r → ℝ)).prod 0) v :=
      (hasFDerivAt_id v).prodMk (hasFDerivAt_const ũ.2 v)
    have hout : HasFDerivAt g (fderiv ℝ g (v, ũ.2)) ((fun x : Fin r → ℝ => (x, ũ.2)) v) :=
      ((hg.differentiable one_ne_zero) (v, ũ.2)).hasFDerivAt
    have h : HasFDerivAt F ((fderiv ℝ g (v, ũ.2)).comp
        ((ContinuousLinearMap.id ℝ (Fin r → ℝ)).prod 0)) v := hout.comp v hin
    rw [h.fderiv]
    rfl
  have hv₂ : ∀ v ∈ Icc lo₁ hi₁, (v, ũ.2) ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂ := fun v hv => ⟨hv, hũ.2⟩
  -- (5) at `w = ũ₂` is the Jacobi step on the slice
  set J₂ : Matrix (Fin r) (Fin s) ℝ := fun i l => fderiv ℝ g ũ (0, Pi.single l 1) i
  obtain ⟨v, hv, hFv⟩ := exists_mem_Icc_eq_add_of_jacobi hF hũ.1 (Jlo := J₁lo) (Jhi := J₁hi)
    (fun v hv i j => by rw [hF']; exact hJ₁ _ (hv₂ v hv) i j) (y - g ũ)
    (fun A hA v hv i => ⟨fun h0 => hdiag i (h0 ▸ hA i i), by
      have h := h5 y hy A hA J₂ (fun i l => hJ₂ ũ hũ i l) v hv ũ.2 hũ.2 i
      simpa using h⟩)
  -- its zero is a preimage of `y`
  refine ⟨(v, ũ.2), hv₂ v hv, ?_⟩
  simpa [F] using hFv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
