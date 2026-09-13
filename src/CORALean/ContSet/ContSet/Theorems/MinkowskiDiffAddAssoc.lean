import CORALean.ContSet.ContSet.ContSet

/-!
# Minkowski difference nests over a sum

`minkowskiDiff A (B + C) = minkowskiDiff (minkowskiDiff A B) C`: subtracting a
sum is the same as subtracting one summand and then the other. It is the step
[1, Thm. 1]'s proof calls eq. (6), quoted there from elsewhere as a fact about
arbitrary sets; the identity itself needs nothing about zonotopes, only that
addition in `α` commutes and associates, so it sits here beside `minkowskiDiff`'s
other general facts rather than under `Zonotope/`.

Both directions unfold `minkowskiDiff` for free — membership in a `setOf` is
definitional — and finish by reassociating the sum that is left over.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Subtracting `B + C` is subtracting `B` and then `C`. -/
theorem minkowskiDiff_add_assoc (A B C : Set α) :
    minkowskiDiff A (B + C) = minkowskiDiff (minkowskiDiff A B) C := by -- --- PROOF ---
  ext x
  constructor
  -- one summand at a time: `b + c` is what the left-hand side is handed
  · intro hx c hc b hb
    have h := hx (b + c) (Set.add_mem_add hb hc)
    have e : x + c + b = x + (b + c) := by abel
    rwa [e]
  -- and back, splitting the sum that membership in `B + C` already carries
  · intro hx z hz
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.mp hz
    have h := hx c hc b hb
    have e : x + c + b = x + (b + c) := by abel
    rwa [e] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
