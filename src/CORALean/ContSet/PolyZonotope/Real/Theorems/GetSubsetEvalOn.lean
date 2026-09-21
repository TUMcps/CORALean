import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnUnitBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

/-!
# `getSubset` is exactly the evaluation over a factor sub-box

`getSubset_construct` says this of `subsetAt` and needs `q = 0` to do it,
because `subsetAt` drops the independent block and `getSubset` carries it
through unchanged. At [1, (13)]'s evaluation the hypothesis goes: what
re-parametrizing factor `k` onto `cen ± rad` constructs is what the whole set
denotes there, independent block included.

This is what supplies [1, Thm. 1]'s initial inclusion — the subset named by a
box of factor values, as a polynomial zonotope a run can start from.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `getSubset`'s evaluation at `B` is the original's at the re-parametrized
`B`: `getSubset_subsetAt` with the independent block along for the ride. -/
theorem PolyZonotope.aux_getSubset_evalOn (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (B : Set (Fin pZ.p → ℝ)) : (pZ.getSubset k cen rad).evalOn B
      = pZ.evalOn ((fun b => Function.update b k (cen + rad * b k)) '' B) := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨b, hb, β, hβ, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, β, hβ, by rw [PolyZonotope.getSubset_point]; rfl⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, β, hβ, rfl⟩
    exact ⟨b, hb, β, hβ, by rw [PolyZonotope.getSubset_point]; rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `getSubset` constructs is what the whole set denotes over the factor
sub-box it names. -/
theorem PolyZonotope.getSubset_evalOn (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (hrad : 0 ≤ rad) : (pZ.getSubset k cen rad).construct
      = pZ.evalOn {a | |a k - cen| ≤ rad ∧ ∀ k', k' ≠ k → |a k'| ≤ 1} := by
  rw [← PolyZonotope.evalOn_unitBox, PolyZonotope.aux_getSubset_evalOn]
  exact congrArg pZ.evalOn (PolyZonotope.getSubset_box k hrad)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
