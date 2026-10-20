module

public import CORALean.ContSet.Conversion.Real.Theorems.LevelSetStarSetExact
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.SupportFunction.Real.Theorems.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A star set that is no support function

The arrow of [1, Fig. 1 (Support Functions → Star Sets)] is strict: the star set of the level set
`{α | α₀² - 1 = 0}` on the unit box is `{-1, 1}` (`LevelSet.starSet_exact`), which holds both points
and not their midpoint, while what a support function denotes is convex
(`SupportFunction.convex_construct`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some level-set star set is no support function

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A star set, with a level-set predicate, that no support function denotes. -/
theorem StarSet.exists_not_supportFunction :
    ∃ s : StarSet LevelSet 1, ¬ ∃ S : SupportFunction (Vec ℝ 1), S.construct = s.construct
    := by -- --- PROOF ---
  -- `{-1, 1}` lies in the unit box, which is the star set's box
  have hD : (⟨1, fun x _ => x 0 ^ 2 - 1, fun _ => .eq⟩ : LevelSet 1).construct
      ⊆ (Interval.unit 1).construct := fun x hx => by
    rw [Interval.mem_unit_iff]
    intro k
    have h := hx 0
    simp only [CompOp.holds, Fin.isValue] at h
    rw [Subsingleton.elim k 0, abs_le]
    constructor <;> nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 0 + 1)]
  refine ⟨(⟨1, fun x _ => x 0 ^ 2 - 1, fun _ => .eq⟩ : LevelSet 1).starSet (Interval.unit 1), ?_⟩
  rintro ⟨S, hS⟩
  rw [LevelSet.starSet_exact _ hD] at hS
  -- the two points `1` and `-1` are on the level set, and their midpoint `0` is not
  have h1 : (fun _ => 1 : Vec ℝ 1) ∈ S.construct := hS ▸ (fun _ => by simp [CompOp.holds])
  have h2 : (fun _ => -1 : Vec ℝ 1) ∈ S.construct := hS ▸ (fun _ => by simp [CompOp.holds])
  have h0 := S.convex_construct h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [hS] at h0
  have := h0 0
  simp [CompOp.holds] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
