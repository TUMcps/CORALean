module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `PolyZonotope.squareExample`

The polynomial zonotope `{α² | α ∈ [-1, 1]}` in `ℝ¹`: one dependent factor, one generator `1`
at the exponent `2`, no independent generators. CORA's `isPolytope` [1] answers `false` for it at
its first test, "a variable appears with exponent greater than 1", while the set is the
interval `[0, 1]` (`squareExample_construct`), a polytope
(`references/coverage/contSet/polyZonotope.md`, row `isPolytope`).

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Center `0`, generator `1`, exponent `2`: the points `α²` for `α` between `-1` and `1`. -/
def PolyZonotope.squareExample : PolyZonotope (Vec ℝ 1) where
  p := 1
  h := 1
  q := 0
  c := 0
  G := fun _ _ => 1
  E := fun _ _ => 2
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
