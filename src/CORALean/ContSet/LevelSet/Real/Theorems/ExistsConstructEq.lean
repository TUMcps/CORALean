module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# Every set is a level set

`f` is an arbitrary function, so the indicator `f x = 0` on a set and `1` off it, with the single
comparison `≤ 0`, has exactly that set as its level set. This is what makes the level sets the most
general class: the content of an arrow into them lies in the other direction, in what a level set
is not.

This is the arrow from polynomial zonotopes to level sets of
[1, Fig. 1 (Polynomial Zonotopes → Level Sets)], and the equivalence of star sets and level sets of
[1, Fig. 1 (Star Sets ↔ Level Sets)].

## Inputs
* `S` – set

## Hypotheses
* none

## Conclusion
* some level set denotes `S`

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.exists_construct_eq (S : Set (Vec ℝ n)) :
    ∃ L : LevelSet n, L.construct = S := by
  classical
  refine ⟨⟨1, fun x _ => if x ∈ S then 0 else 1, fun _ => .le⟩, ?_⟩
  ext x
  by_cases hx : x ∈ S <;> simp [LevelSet.construct, CompOp.holds, hx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
