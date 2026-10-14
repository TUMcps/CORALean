module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# Splitting a bundle is exact

[1, Eq. 2]: the two halves `Z_∩ ∩ Ψ₁` and `Z_∩ ∩ Ψ₂` cover `Z_∩` exactly, for any invertible
`Λ` and any box `B` enclosing `Λ⁻¹ Z_∩` — "no matter how the other column vectors of `Λ` besides the
`j`-th one are chosen and how tightly `box()` is obtained". The enclosure `Z_∩ ⊆ Ψ` is what makes
`Z_∩ ∩ Ψ = Z_∩`, and `Zonotope.split_union` covers `Ψ` by its halves.
The printed `Z_∩¹ ∩ Z_∩² = ∅` is false; `split_inter` says what the halves share.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The halves of the split cover the bundle, exactly, whenever `B` encloses `Λ⁻¹ Z_∩`. -/
theorem ZonoBundle.split_union (Λ : Mat ℝ n n) (hΛ : IsUnit Λ.det) (B : Interval (Vec ℝ n))
    (j : Fin n) (zB : ZonoBundle (Vec ℝ n))
    (hB : (fun x => Λ⁻¹ *ᵥ x) '' zB.construct ⊆ B.construct) :
    (zB.split Λ B j).fst.construct ∪ (zB.split Λ B j).snd.construct
      = zB.construct := by -- --- PROOF ---
  -- a one-member bundle denotes its member
  have hconst : ∀ Z : Zonotope (Vec ℝ n), (ZonoBundle.mk 1 fun _ => Z).construct = Z.construct :=
    fun Z => by
      show (⋂ _ : Fin 1, Z.construct) = Z.construct
      exact Set.iInter_const Z.construct
  -- the bundle lies in `Ψ`: `Λ⁻¹ x` is in the box, so in its zonotope, and `Λ` maps it back
  have hsub : zB.construct ⊆ (ZonoBundle.parallelotope Λ B).construct := by
    intro x hx
    rw [ZonoBundle.parallelotope, ← Zonotope.mtimes_exact]
    refine ⟨Λ⁻¹ *ᵥ x, Interval.zonotope_contains B (hB ⟨x, hx, rfl⟩), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΛ]
  simp only [ZonoBundle.split, ZonoBundle.intersection_exact, hconst]
  rw [← Set.inter_union_distrib_left, Zonotope.split_union]
  exact Set.inter_eq_left.2 hsub

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
