module

public import CORALean.ContSet.Interval.Real.Operations.Times

@[expose] public section

/-!
# `Interval.prod₁`

CORA's `@interval/prod` of an interval matrix along dimension 1: the rows are multiplied
together entrywise with the interval product `.*` (`times`), `res = res .* I(i, :)` for
`i = 2 : m`. CORA keeps the result as a `1 × n` matrix; here it is the vector of the same entries.
The fold starts at the point `1`, the empty product, where CORA starts at the first row; the two
agree for `m ≥ 1` since `1 .* r = r`.

## Inputs
* `I` – interval matrix

## Output
* box of the entrywise product of the rows
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows multiplied together by `times`, the last row first. -/
def Interval.prod₁ (I : Interval (Mat ℝ m n)) : Interval (Vec ℝ n) :=
  -- row `i` of the interval matrix, `I(i, :)`
  let row : Fin m → Interval (Vec ℝ n) := fun i => ⟨fun j => I.inf i j, fun j => I.sup i j⟩
  Fin.foldr m (fun i res => (row i).times res) (Interval.point (fun _ => 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
