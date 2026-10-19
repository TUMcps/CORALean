module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirPca

@[expose] public section

/-!
# Splitting by the pca heuristic is exact

[1, Heuristic pca] claims no property of its axes beyond their variance. What the split needs of
`Λ` is invertibility, which holds because Mathlib's eigenvector matrix is unitary.

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

/-- The pca heuristic's split is exact, at any vertex cloud. -/
theorem ZonoBundle.splitPca_union {m : ℕ} (V : Fin m → Vec ℝ n) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) (j : Fin n) : -- --- STMT ---
    (zB.split (ZonoBundle.dirPca V) (zB.enclosingBox (ZonoBundle.dirPca V) i) j).fst.construct
      ∪ (zB.split (ZonoBundle.dirPca V) (zB.enclosingBox (ZonoBundle.dirPca V) i) j).snd.construct
      = zB.construct :=
  ZonoBundle.split_union_enclosingBox _ (Matrix.UnitaryGroup.det_isUnit _) zB i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
