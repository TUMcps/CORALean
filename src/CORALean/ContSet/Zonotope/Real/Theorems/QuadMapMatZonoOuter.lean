import CORALean.ContSet.Zonotope.Real.Operations.QuadMapMatZono
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapOuter
import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter

/-!
# The quadratic map at a matrix zonotope is enclosed by `Zonotope.quadMapMatZono`

[1, Thm. 1], by the printed proof, eq. (12): `xᵀ(D⁽ⁱ⁾ + Σⱼ βⱼK⁽ⁱ'ʲ⁾)x = xᵀD⁽ⁱ⁾x + Σⱼ βⱼ xᵀK⁽ⁱ'ʲ⁾x`,
the first a point of `Z_D` and each `βⱼ xᵀK⁽ⁱ'ʲ⁾x` a point of `[-1, 1] ⊗ Z_K(j)`, by
[1, Lemma 1] and [1, Eq. 11]; the coefficients of the `ν + 1` parts are then the sum's.

The factor `βⱼ` is one per `j`, the same for every coordinate `i` — what eq. (12) writes,
and what the application in Sec. 5.4 has, its matrices all depending on one `x₀`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m ν : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], factors shared across coordinates: `{λ | λᵢ = xᵀ(D⁽ⁱ⁾ + Σⱼ βⱼK⁽ⁱ'ʲ⁾)x}`
lies in `Z.quadMapMatZono D K`. -/
theorem Zonotope.quadMapMatZono_outer (D : Fin m → Mat ℝ n n)
    (K : Fin ν → Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    {l : Vec ℝ m | ∃ x ∈ Z.construct, ∃ β : Fin ν → ℝ, (∀ j, |β j| ≤ 1) ∧
        ∀ i, l i = x ⬝ᵥ ((D i + ∑ j, β j • K j i) *ᵥ x)}
      ⊆ (Z.quadMapMatZono D K).construct := by -- --- PROOF ---
  rintro l ⟨x, hx, β, hβ, hl⟩
  -- the centres' part, a point of `Z_D`
  obtain ⟨γ, hγ, hD⟩ := Z.quadMap_outer D ⟨x, hx, rfl⟩
  -- each generator's part, `βⱼ xᵀK⁽ʲ⁾x`, a point of `[-1, 1] ⊗ Z_K(j)`
  have hK : ∀ j, ∃ δ : Fin (Z.h + Z.h + Z.h * Z.h + 1) → ℝ, (∀ k, |δ k| ≤ 1) ∧
      β j • (fun i => x ⬝ᵥ (K j i *ᵥ x))
        = (0 : Vec ℝ m) + ∑ k, δ k • ((Z.quadMap (K j)).unitIntervalMul.G k) := fun j =>
    (Z.quadMap (K j)).unitIntervalMul_outer
      ⟨(β j, _), ⟨abs_le.mp (hβ j), Z.quadMap_outer (K j) ⟨x, hx, rfl⟩⟩, rfl⟩
  choose δ hδ hKeq using hK
  refine ⟨Fin.append γ fun k => δ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
    Fin.addCases (fun k => by rw [Fin.append_left]; exact hγ k)
      (fun k => by rw [Fin.append_right]; exact hδ _ _), ?_⟩
  -- eq. (12): the centre's quadratic form plus every generator's, scaled by its factor
  have hsplit : l = (fun i => x ⬝ᵥ (D i *ᵥ x)) + ∑ j, β j • (fun i => x ⬝ᵥ (K j i *ᵥ x)) := by
    funext i
    rw [hl i, Pi.add_apply, Finset.sum_apply, add_mulVec, dotProduct_add, Matrix.sum_mulVec,
      dotProduct_sum]
    simp only [Pi.smul_apply, smul_eq_mul, smul_mulVec, dotProduct_smul]
  show l = (Z.quadMap D).c + ∑ k, (Fin.append γ fun k =>
      δ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) k
    • (Fin.append (Z.quadMap D).G fun k =>
        ((Z.quadMap (K (finProdFinEquiv.symm k).1)).unitIntervalMul).G
          (finProdFinEquiv.symm k).2) k
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  -- the generators' block, read over `Fin ν × Fin (p + p + p² + 1)`
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun jk : Fin ν × Fin (Z.h + Z.h + Z.h * Z.h + 1) =>
      δ jk.1 jk.2 • (Z.quadMap (K jk.1)).unitIntervalMul.G jk.2) fun _ => rfl,
    Fintype.sum_prod_type]
  simp only [zero_add] at hKeq
  have hD' : (fun i => x ⬝ᵥ (D i *ᵥ x)) = (Z.quadMap D).c + ∑ j, γ j • (Z.quadMap D).G j := hD
  rw [hsplit, hD', add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun j _ => hKeq j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
