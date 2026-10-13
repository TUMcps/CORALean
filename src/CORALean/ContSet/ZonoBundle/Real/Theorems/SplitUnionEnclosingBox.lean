module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingBoxContains

@[expose] public section

/-!
# Splitting at the computed box is exact

`split_union` with its hypothesis on the box discharged: the box CORA computes, `enclosingBox`,
always encloses `Λ⁻¹ Z_∩`. So [1, Eq. 2] as an algorithm needs only an invertible `Λ`.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2] at the computed box: exact for every invertible `Λ`, member `i` and column `j`. -/
theorem ZonoBundle.split_union_enclosingBox (Λ : Mat ℝ n n) (hΛ : IsUnit Λ.det)
    (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) (j : Fin n) :
    (zB.split Λ (zB.enclosingBox Λ i) j).1.construct
      ∪ (zB.split Λ (zB.enclosingBox Λ i) j).2.construct = zB.construct :=
  ZonoBundle.split_union Λ hΛ _ j zB (ZonoBundle.enclosingBox_contains Λ zB i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
