module

public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStripFamily
public import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectStripExact

@[expose] public section

/-!
# `ConZonotope.intersectStripFamily` is exactly the intersection with the family of strips

[1, Lemma 2]: the family is `intersectStrip` at the stacked strip, `C` the `H_j` one below the
other, `φ` the `r_j` repeated `p` times, `Λ = [λ_1 … λ_m]`, so `intersectStrip_exact` applies. The
radii are nonnegative (`0 ≤ r_j`): the paper takes them as radii and does not say so, and at a
negative radius the strip is empty while the new factor would still reach points.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stacked strip: the `H_j` below one another, the radii repeated, the gains side by side. -/
theorem ConZonotope.aux_family_eq_stacked (cZ : ConZonotope (Vec ℝ n)) (H : Fin m → Mat ℝ p n)
    (r : Fin m → ℝ) (y : Fin m → Vec ℝ p) (lam : Fin m → Mat ℝ n p) :
    cZ.intersectStripFamily H r y lam =
      cZ.intersectStrip
        (Matrix.of fun q a => H (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 a)
        (fun q => r (finProdFinEquiv.symm q).1)
        (fun q => y (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
        (Matrix.of fun a q =>
          lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2) := by -- --- PROOF ---
  -- the same constraints and generator count; the center and old generators are sums over `j`
  have hsum : ∀ (M : Fin (m * p) → Fin n → ℝ) (f : Fin m → Fin p → ℝ) (a : Fin n),
      (∑ j, ∑ k, M (finProdFinEquiv (j, k)) a * f j k) =
        ∑ q, M q a * f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 := by
    intro M f a
    -- the stacked index runs over the pairs
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
  have hc : ∀ (v : Fin m → Vec ℝ p),
      ∑ j, lam j *ᵥ v j = Matrix.of (fun a q => lam (finProdFinEquiv.symm q).1 a
        (finProdFinEquiv.symm q).2) *ᵥ fun q => v (finProdFinEquiv.symm q).1
          (finProdFinEquiv.symm q).2 := by
    intro v
    funext a
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← hsum (fun q a => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2) v a]
    simp only [Equiv.symm_apply_apply]
  -- the gains and strips stacked multiply out to the sum of the products
  have hGm : (∑ j, lam j * H j) =
      Matrix.of (fun a q => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2) *
        Matrix.of fun q a => H (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 a := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
  unfold ConZonotope.intersectStripFamily ConZonotope.intersectStrip
  congr 1
  · rw [hc fun j => y j - H j *ᵥ cZ.c]
    rfl
  · rw [hGm]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersectStripFamily_exact (cZ : ConZonotope (Vec ℝ n))
    (H : Fin m → Mat ℝ p n) (r : Fin m → ℝ) (y : Fin m → Vec ℝ p) (lam : Fin m → Mat ℝ n p)
    (hr : ∀ j, 0 ≤ r j) :
    (cZ.intersectStripFamily H r y lam).construct =
      cZ.construct ∩ {x | ∀ j k, |(H j *ᵥ x - y j) k| ≤ r j} := by -- --- PROOF ---
  rw [ConZonotope.aux_family_eq_stacked, ConZonotope.intersectStrip_exact _ _ _ _ _
    fun q => hr _]
  -- the stacked strip rows are the strip rows of every `j`, read through the index equivalence
  have key : ∀ P : Fin m → Fin p → Prop,
      (∀ q, P (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) ↔ ∀ j k, P j k :=
    fun P => ⟨fun h j k => by simpa using h (finProdFinEquiv (j, k)), fun h q => h _ _⟩
  ext x
  exact and_congr_right fun _ => key fun j k => |(H j *ᵥ x - y j) k| ≤ r j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
