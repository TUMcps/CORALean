module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# A convex minuend needs only the vertices of the subtrahend

For a convex `S` and `P = ⟨V⟩_V`, `minkowskiDiff S P.construct = ⋂ i, {x | x + V i ∈ S}`: a point
`x + p` for `p ∈ P.construct` is a convex combination of the points `x + V i`, so if each of those
already lies in `S`, convexity puts the whole combination there too — checking every `p ∈ P`
collapses to checking every vertex.

The step [1, Prop. 6]'s proof takes at `Z ⊖ P = ⋂ᵢ (Z − vᵢ)`, stated for any convex set rather than
only a zonotope, and needless of `P.k > 0`: at `P.k = 0`, `P.construct` and the intersection are
both `Set.univ` (a subtrahend `∅` moves nothing, and no side of `⋂ i : Fin 0, ·` names a condition).

## Inputs
* `S` – convex minuend
* `P` – polytope

## Hypotheses
* `hS` – `S` convex

## Conclusion
* the difference is the intersection of `S - vᵢ` over the vertices

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6]'s `Z ⊖ P = ⋂ᵢ (Z − vᵢ)`, for any convex minuend. -/
theorem VPolytope.minkowskiDiff_eq_iInter {S : Set α} (hS : Convex ℝ S)
    (P : VPolytope α) : -- --- CONCL ---
    minkowskiDiff S P.construct = ⋂ i, {y | y + P.V i ∈ S} := by -- --- PROOF ---
  ext x
  simp only [minkowskiDiff, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · exact fun h i => h (P.V i) ⟨fun j => if j = i then 1 else 0, by aesop, by simp, by simp⟩
  · rintro h y ⟨β, hβ0, hβ1, rfl⟩
    have hmem : ∀ i, x + P.V i ∈ S := h
    have hsum := hS.sum_mem (t := Finset.univ) (fun i _ => hβ0 i) hβ1 (fun i _ => hmem i)
    have heq : (∑ i, β i • (x + P.V i)) = x + ∑ i, β i • P.V i := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hβ1, one_smul]
    rwa [heq] at hsum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
