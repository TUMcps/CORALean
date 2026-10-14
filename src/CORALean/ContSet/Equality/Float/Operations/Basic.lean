module

public import CORALean.ContSet.ContSet.Operations.Basic

@[expose] public section

/-!
# `ContSet/Equality/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open CORALean

variable {S α : Type} [ContSet S α] [Isequal S] [DecidableRel (Isequal.isequal (S := S))]


-- =====================================  `ContSet.eqBool`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ContSet.eq` is a `Prop`; this reads it as a run: the class's conservative `isequal`, decided.
For a float representation the `isequal` is the certified structural test, so `true` is a proof
that the two sets are equal and `false` refutes nothing. -/
def ContSet.eqBool (s t : S) : Bool := decide (Isequal.isequal s t)


-- =====================================  `ContSet.neBool`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The negation of `ContSet.eqBool`, as CORA's `ne` is `~isequal`. -/
def ContSet.neBool (s t : S) : Bool := !ContSet.eqBool s t

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
