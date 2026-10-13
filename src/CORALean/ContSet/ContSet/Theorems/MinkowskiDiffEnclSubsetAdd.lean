import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd

/-!
# Splitting the minuend into an enclosure and a remainder loses no room

[1, Prop. 4]: at `A := Zmencl`, `B := Zmrem`, `C := Zs`,
`minkowskiDiff_add_subset_add` already says exactly this — the corollary below
is the specialization to the paper's own names, kept as its own row since the
paper states it as its own proposition.

`_hencl : Zs ⊆ Zmencl` is the paper's own hypothesis, carried for fidelity to
[1, Prop. 4]'s statement even though the algebra needs neither it nor
convexity, exactly as `minkowskiDiff_add_subset_add`'s docstring already says.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4]: enclosing the subtrahend in part of the minuend and
splitting off the rest changes nothing that a Minkowski difference sees. -/
theorem minkowskiDiff_encl_subset_add (Zmencl Zmrem Zs : Set α) (_hencl : Zs ⊆ Zmencl) :
    minkowskiDiff Zmencl Zs + Zmrem ⊆ minkowskiDiff (Zmencl + Zmrem) Zs :=
  minkowskiDiff_add_subset_add Zmencl Zmrem Zs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
