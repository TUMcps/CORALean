module

public import CORALean.ContSet.ConZonotope.Float.Operations.Compact
public import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
public import CORALean.ContSet.Zonotope.Float.Operations.GirardKeep

@[expose] public section

/-!
# `ConZonotope.reduce` over a floating-point scalar

CORA's `@conZonotope/reduce` with Girard's rule [1, Sec. 4.3] on the stored floats, the steps of
the real `ConZonotope.reduce`: `compact`, `liftEq` (centered at `[c; 0]`, the interval `bₑ` kept
beside it), Girard's ranking computed in `𝕋` (`girardKeep`), so the two layers may keep different
generators, and `reduceLiftBy`. The box is rounded up, so the result is outer (`reduce_outer`).

## Inputs
* `cZ` – float constrained zonotope
* `o` – target degree-of-freedom order

## Output
* enclosing constrained zonotope of reduced order

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(cZ, 'girard', o)` in floats: Girard's rule on the zonotope `[G; Aₑ]` the equality
rows lift to, the rows read back off the result. -/
def ConZonotope.reduce (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- 1. without the zero constraint rows and the zero generators
  let cZ := cZ.compact
  -- 2. the lifted zonotope `Z_up = ⟨[c; 0], [G; Aₑ]⟩`, `bₑ` an interval kept beside it
  let Z_up := cZ.liftEq
  -- 3. at `order = max(1, (o n + mₑ)/(n + mₑ))` Girard keeps `(n + mₑ)(order - 1) = (o - 1) n`
  let nUnreduced := (o - 1) * n
  -- ... once there are more than `(n + mₑ) order = max(o, 1) n + mₑ` generators
  if hlt : max o 1 * n + cZ.P.me < cZ.h then
    -- 4. and 5. reduce `Z_up` by Girard's ranking and read `G` and `Aₑ` back off it
    cZ.reduceLiftBy (Z_up.girardKeep nUnreduced
      (le_of_lt (lt_of_le_of_lt (le_trans (Nat.mul_le_mul_right n (by omega))
        (Nat.le_add_right _ _)) hlt)))
  else cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
