module

public import CORALean.Global.DropIdx
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ConPolyZono.reduceConG`

The generator matrix of [1, Prop. 13]. Generator `d` goes, and one generator per
surviving constraint generator takes its place: the eliminated constraint row
solves for `d`'s monomial, and what comes back in its stead is `G d` scaled by
`-A(r,i)/A(r,t)`, one column for each constraint generator `i` still standing.

[1] writes the replacement block where column `d` stood. Here the surviving
columns come first and the block after, `dropIdx` enumerating in order: a
generator sum does not read its index, so the two lay out the same set.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators that survive, then `G d` once per surviving constraint
generator, scaled by what the eliminated row gives it. -/
noncomputable def ConPolyZono.reduceConG {α : Type} [AddCommGroup α] [Module ℝ α]
    {h m q : ℕ} (G : Fin h → α) (A : Mat ℝ m q) (r : Fin m) (d : Fin h) (t : Fin q) :
    Fin ((h - 1) + (q - 1)) → α :=
  Fin.addCases (fun i => G (dropIdx d i)) (fun i => (-(A r (dropIdx t i)) / A r t) • G d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
