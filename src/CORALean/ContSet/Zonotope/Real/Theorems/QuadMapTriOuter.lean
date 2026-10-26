module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapTri
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapOuter
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.quadMapTri` encloses the quadratic map

[1, Lemma 1 (generators)] with the `σ = C(p + 2, 2) - 1` generators it prints. `quadMap`'s pair
block runs over all of `Fin p × Fin p` and is zero off `j < k`, so a coefficient vector of `quadMap`
gives one of `quadMapTri`: keep the linear and square blocks, and give pair `l` the coefficient of
its `(j, k)`. The zero generators carry no weight. With `quadMap_outer` that is the lemma's
enclosure.

## Inputs
* `n` – dimension
* `m` – output dimension
* `Q` – family of quadratic matrices
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the quadratic images lie in the triangular result

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `quadMap`'s set is inside `quadMapTri`'s: the pair block re-indexed by `j < k` alone. -/
private theorem Zonotope.aux_quadMap_subset_quadMapTri {n m : ℕ} (Q : Fin m → Mat ℝ n n)
    (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (Z.quadMap Q).construct ⊆ (Z.quadMapTri Q).construct := by -- --- PROOF ---
  rintro x ⟨(β : Fin (Z.h + Z.h + Z.h * Z.h) → ℝ), hβ, rfl⟩
  set e := Zonotope.aux_quadMapPairIdx Z.h with he
  -- the pair generator of `(j, k)`, coordinate `i`
  set g : Fin Z.h × Fin Z.h → Fin m → ℝ := fun jk i =>
    Z.G jk.1 ⬝ᵥ (Q i *ᵥ Z.G jk.2) + Z.G jk.2 ⬝ᵥ (Q i *ᵥ Z.G jk.1) with hg
  set b : Fin Z.h × Fin Z.h → ℝ := fun jk => β (Fin.natAdd (Z.h + Z.h) (finProdFinEquiv jk))
    with hb
  refine ⟨Fin.append (fun a => β (Fin.castAdd (Z.h * Z.h) a)) (fun l => b (e l).1),
    fun a => ?_, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun l => ?_) a
    · rw [Fin.append_left]; exact hβ _
    · rw [Fin.append_right]; exact hβ _
  · -- the two linear-and-square blocks agree; the pair blocks agree once re-indexed
    dsimp only [Zonotope.quadMap, Zonotope.quadMapTri]
    show _ + ∑ a : Fin (Z.h + Z.h + Z.h * Z.h), β a • _
      = _ + ∑ a : Fin (Z.h + Z.h + Z.h.choose 2), _ • _
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    congr 2
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- `quadMap`'s pair block: over `Fin p × Fin p`, zero off `j < k`
    show ∑ l : Fin (Z.h * Z.h), β (Fin.natAdd (Z.h + Z.h) l) *
        (if (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2 then
          g (finProdFinEquiv.symm l) i else 0)
      = ∑ l : Fin (Z.h.choose 2), b (e l).1 * g (e l).1 i
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, mul_ite, mul_zero]
    rw [← Finset.sum_filter, ← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply]
    rw [Finset.sum_subtype (p := fun jk : Fin Z.h × Fin Z.h => jk.1 < jk.2)
      (Finset.univ.filter fun jk : Fin Z.h × Fin Z.h => jk.1 < jk.2) (fun jk => by simp)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1 (generators)]: `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z} ⊆ Z.quadMapTri Q`, `σ = C(p + 2, 2) - 1`
generators. -/
theorem Zonotope.quadMapTri_outer {n m : ℕ} (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (Q i *ᵥ x)) '' Z.construct
      ⊆ (Z.quadMapTri Q).construct :=
  (Zonotope.quadMap_outer Q Z).trans (Zonotope.aux_quadMap_subset_quadMapTri Q Z)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
