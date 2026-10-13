module

public import CORALean.ContSet.VPolytope.Real.Operations.Bilin

@[expose] public section

/-!
# `VPolytope.bilin` encloses every pointwise product

Nothing is over-approximated here, only unproven: in the vertex representation
the products `λᵢμⱼ` really are the coefficients of a convex combination, so
every `f a b` with `a ∈ P.construct`, `b ∈ Q.construct` *is* a convex
combination of the pairwise vertex products, and each vertex of the result is
attained. Contrast `PolyZonotope.bilin`, exact for a different reason — shared
factors and an exponent matrix — and #81's `Zonotope.bilin`, which genuinely
enlarges because a zonotope cannot record that `αᵢβⱼ` depends on both `αᵢ` and
`βⱼ`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem VPolytope.aux_bilin_V (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : VPolytope α) (Q : VPolytope β)
    (m : Fin (P.k * Q.k)) :
    (VPolytope.bilin f P Q).V m
      = f (P.V (finProdFinEquiv.symm m).1) (Q.V (finProdFinEquiv.symm m).2) :=
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.bilin_outer (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : VPolytope α) (Q : VPolytope β) :
    (⋃ a ∈ P.construct, (f a ·) '' Q.construct)
      ⊆ (VPolytope.bilin f P Q).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨a, ⟨lam, hlam0, hlam1, rfl⟩, b, ⟨mu, hmu0, hmu1, rfl⟩, rfl⟩ := hy
  -- `show` fixes the witness type to `Fin (P.k * Q.k)`, only defeq to `(bilin f P Q).k`
  show ∃ w : Fin (P.k * Q.k) → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1
    ∧ f (∑ i, lam i • P.V i) (∑ j, mu j • Q.V j) = ∑ j, w j • (VPolytope.bilin f P Q).V j
  refine ⟨fun m => mu (finProdFinEquiv.symm m).2 * lam (finProdFinEquiv.symm m).1, ?_, ?_, ?_⟩
  · exact fun j => mul_nonneg (hmu0 _) (hlam0 _)
  · -- the products sum to one: regroup as a product of the two vertex sums
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type' (f := fun i j => mu j * lam i), Finset.sum_comm,
      ← Fintype.sum_mul_sum, hmu1, hlam1, mul_one]
  · -- bilinearity pushes `f` through both sums; `a`'s is named below, since the root matches
    simp only [VPolytope.aux_bilin_V]
    conv_lhs => rw [show f (∑ i, lam i • P.V i) = ∑ i, lam i • f (P.V i) from by
      rw [map_sum]; simp only [map_smul]]
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, map_sum, map_smul, smul_smul]
    rw [← Fintype.sum_prod_type' (f := fun i j => (mu j * lam i) • f (P.V i) (Q.V j)),
      ← finProdFinEquiv.symm.sum_comp
        (fun p : Fin P.k × Fin Q.k => (mu p.2 * lam p.1) • f (P.V p.1) (Q.V p.2))]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
