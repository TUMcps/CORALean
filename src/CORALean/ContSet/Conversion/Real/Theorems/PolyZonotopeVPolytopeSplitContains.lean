module

public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.Global.Corners
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeVPolytopeCornersContainsOfBinary
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as its corners

Two enclosures, the cheaper first. `vPolytope` goes through the zonotope
enclosure and then that zonotope's `2ʰ` sign corners, losing whatever the
zonotope step lost and nothing further.

`vPolytopeSplit` is [1, Prop. 6], which splits the exponent matrix instead. A
column whose exponents are all at most one is multilinear in the factors, and a
multilinear map on a box is a convex combination of its values at the box's
corners — so such a column is read at every sign vector of the factors exactly.
Only a column with an exponent above one is given up, to `zonotopeEven`. That is
all the vertex enumeration the paper defers to a companion algorithm comes to
here: its closing convex hull only drops points that are not vertices.

Neither is exact, a polynomial zonotope being generally non-convex. The paper
deletes the columns it gives up; here they stay at a zero generator, which costs
vertices and not precision.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_binarize_E_le (pZ : PolyZonotope α) (k : Fin pZ.binarize.p)
    (i : Fin pZ.binarize.h) : pZ.binarize.E k i ≤ 1 := by
  show (if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) ≤ 1
  split_ifs with h
  · exact h k
  · exact Nat.zero_le 1

theorem PolyZonotope.aux_binarize_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.binarize.construct := by -- --- PROOF ---
  rintro _ ⟨a, β, ha, hb, rfl⟩
  -- what the given-up columns and the independent block reach is a zonotope's
  have hmem : (0 : α) + ∑ i, PolyZonotope.monomial pZ.E a i
        • (if ∀ k, pZ.E k i ≤ 1 then (0:α) else pZ.G i)
      + ∑ j, β j • pZ.GI j ∈ pZ.high.construct := ⟨a, β, ha, hb, rfl⟩
  obtain ⟨γ, hγ, hγeq⟩ := pZ.high.zonotopeEven_contains hmem
  rw [zero_add] at hγeq
  refine ⟨a, γ, ha, hγ, ?_⟩
  -- every column lands in exactly one of the two blocks
  have hsplit : ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
      = ∑ i, PolyZonotope.monomial (fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) a i
            • (if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0)
        + ∑ i, PolyZonotope.monomial pZ.E a i
            • (if ∀ k, pZ.E k i ≤ 1 then (0:α) else pZ.G i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hbin : ∀ k, pZ.E k i ≤ 1
    · -- a kept column keeps its exponents, so its monomial is the one it had
      rw [if_pos hbin, if_pos hbin, smul_zero, add_zero]
      exact congrArg (· • pZ.G i)
        (Finset.prod_congr rfl fun k _ => congrArg (a k ^ ·) (if_pos hbin).symm)
    · rw [if_neg hbin, if_neg hbin, smul_zero, zero_add]
  show pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, β j • pZ.GI j
      = pZ.c + pZ.high.zonotopeEven.c
        + ∑ i, PolyZonotope.monomial (fun k i => if ∀ k', pZ.E k' i ≤ 1 then pZ.E k i else 0) a i
            • (if ∀ k, pZ.E k i ≤ 1 then pZ.G i else 0)
        + ∑ l, γ l • pZ.high.zonotopeEven.G l
  rw [hsplit, add_assoc, add_assoc, hγeq]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.vPolytopeSplit_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.vPolytopeSplit.construct :=
  subset_trans pZ.aux_binarize_contains
    (PolyZonotope.vPolytopeCorners_contains_of_binary _ pZ.aux_binarize_E_le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
