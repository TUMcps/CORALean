module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitIntersection
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact

@[expose] public section

/-!
# What the halves of a split bundle share

[1, Eq. 2] prints `Z_∩¹ ∩ Z_∩² = ∅`. Closed sets that cover a set and are cut by a hyperplane
share the cut, so it is false (`split_not_disjoint`). What holds is that the halves meet in the
bundle intersected with `Ψ` with its `j`-th generator dropped, which is
`Zonotope.split_intersection`.

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

/-- The halves of a split bundle meet in `Z_∩` cut with `Ψ`, its `j`-th generator set to `0`. -/
theorem ZonoBundle.split_inter (Λ : Mat ℝ n n) (B : Interval (Vec ℝ n)) (j : Fin n)
    (zB : ZonoBundle (Vec ℝ n)) :
    (zB.split Λ B j).fst.construct ∩ (zB.split Λ B j).snd.construct = zB.construct ∩
      ({ZonoBundle.parallelotope Λ B with G := Function.update (ZonoBundle.parallelotope Λ B).G j 0}
        : Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  have hconst : ∀ Z : Zonotope (Vec ℝ n), (ZonoBundle.mk 1 fun _ => Z).construct = Z.construct :=
    fun Z => by
      show (⋂ _ : Fin 1, Z.construct) = Z.construct
      exact Set.iInter_const Z.construct
  simp only [ZonoBundle.split, ZonoBundle.intersection_exact, hconst]
  rw [← Set.inter_inter_distrib_left, Zonotope.split_intersection]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
