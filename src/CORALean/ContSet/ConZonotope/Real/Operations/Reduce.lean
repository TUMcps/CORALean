module

public import CORALean.ContSet.ConZonotope.Real.Operations.Compact
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLiftBy
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.GirardKeep

@[expose] public section

/-!
# `ConZonotope.reduce`

CORA's `@conZonotope/reduce` with Girard's rule [1, Sec. 4.3], one `let` per step: `compact_`,
the lift to `Z_up = ⟨[c; -bₑ], [G; Aₑ]⟩`, the order scaled to `max(1, (o n + mₑ)/(n + mₑ))`,
Girard's rule on `Z_up` and the rows read back. At that order Girard keeps `(o - 1) n` generators
once there are more than `max(o, 1) n + mₑ`, both integers, so nothing is rounded. With no equality
rows this is CORA's direct `zonotope(c, G)` branch. The inequality rows, which CORA does not have,
stay on the kept generators, loosened (`keepRows`). Only Girard's box is outer (`reduce_outer`).

## Inputs
* `cZ` – constrained zonotope
* `o` – target degree-of-freedom order

## Output
* enclosing constrained zonotope of reduced order

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       01-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(cZ, 'girard', o)`: Girard's rule on the zonotope `[G; Aₑ]` the equality rows
lift to, the rows read back off the result. -/
noncomputable def ConZonotope.reduce (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  -- 1. without the trivial constraints `0 β = 0` and the zero generators
  let cZ := cZ.compact
  -- 2. the lifted zonotope `Z_up = ⟨[c; -bₑ], [G; Aₑ]⟩`
  let Z_up := cZ.liftEq
  -- 3. at `order = max(1, (o n + mₑ)/(n + mₑ))` Girard keeps `(n + mₑ)(order - 1) = (o - 1) n`
  let nUnreduced := (o - 1) * n
  -- ... once there are more than `(n + mₑ) order = max(o, 1) n + mₑ` generators
  if hlt : max o 1 * n + cZ.P.me < cZ.h then
    -- 4. and 5. reduce `Z_up` by Girard's ranking and read `G` and `Aₑ` back off it
    cZ.reduceLiftBy (Z_up.zonotope.girardKeep nUnreduced
      (le_of_lt (lt_of_le_of_lt (le_trans (Nat.mul_le_mul_right n (by omega))
        (Nat.le_add_right _ _)) hlt)))
  else cZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
