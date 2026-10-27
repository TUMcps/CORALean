module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.StarSet.Real.Instances
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A level set that is no star set of CORA's predicate

A star set `{c + G α | C α ≤ d, l ≤ α ≤ u}`, its predicate an `HPolytope`, is convex
(`StarSet.convex_construct`), and a level set
need not be: `{x | x₀² - 1 = 0} = {-1, 1}` contains the two points and not their midpoint. So the
equivalence of star sets and level sets of [1, Fig. 1 (Star Sets ↔ Level Sets)] needs a predicate
beyond the linear one: with a level-set predicate it holds for bounded level sets
(`LevelSet.starSet_exact`, `StarSet.exists_levelSet_exact`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some level set on the line is no star set with polytope predicate

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{-1, 1}` is a level set and no star set with a polytope predicate. -/
theorem LevelSet.exists_not_starSet_hPolytope : -- --- CONCL ---
    ∃ L : LevelSet 1, ¬ ∃ s : StarSet ℋ𝒫 1, s.construct = L.construct
    := by -- --- PROOF ---
  refine ⟨⟨1, fun x _ => x 0 ^ 2 - 1, fun _ => .eq⟩, ?_⟩
  rintro ⟨s, hs⟩
  -- the two points `1` and `-1` are on the level set, and `0` is not
  have h1 : (fun _ => 1 : Vec ℝ 1) ∈ s.construct := hs ▸ (fun _ => by simp [CompOp.holds])
  have h2 : (fun _ => -1 : Vec ℝ 1) ∈ s.construct := hs ▸ (fun _ => by simp [CompOp.holds])
  have h0 := s.convex_construct h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [hs] at h0
  have := h0 0
  simp [CompOp.holds] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
