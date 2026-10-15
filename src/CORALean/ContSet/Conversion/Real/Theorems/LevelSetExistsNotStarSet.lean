module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.StarSet.Real.Theorems.Convex
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A level set that is no star set

A star set `{c + G α | C α ≤ d, l ≤ α ≤ u}` is convex (`StarSet.convex_construct`), and a level set
need not be: `{x | x₀² - 1 = 0} = {-1, 1}` contains the two points and not their midpoint. So a
level set is no star set, though every star set is a level set (`LevelSet.exists_construct_eq`).

This is the equivalence of star sets and level sets of [1, Fig. 1 (Star Sets ↔ Level Sets)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.exists_not_starSet :
    ∃ L : LevelSet 1, ¬ ∃ s : StarSet 1, s.construct = L.construct := by -- --- PROOF ---
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
