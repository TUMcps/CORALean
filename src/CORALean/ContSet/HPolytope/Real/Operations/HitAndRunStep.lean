module

public import CORALean.ContSet.HPolytope.Real.Operations.ChordHigh
public import CORALean.ContSet.HPolytope.Real.Operations.ChordLow

@[expose] public section

/-!
# `HPolytope.hitAndRunStep`

`[1, Sec. 3, Mixing Algorithm, step 2]` for the random-directions algorithm: given the random
direction `d`, find the line set `L = S ∩ {x + t d}` and take `X_{i+1}` uniformly on it. `L` is the
chord `[t̲, t̄]` of `[2, Eq. 1]`, which for a bounded polytope is exact at an interior point, and
the uniform draw is `x + (t̲ + u (t̄ - t̲)) d` for `u` uniform on `[0, 1]`. The two random inputs,
`d` and `u`, are arguments; `none` is an unbounded chord, where no uniform draw exists.

## Inputs
* `P` – H-polytope
* `x` – point
* `d` – direction
* `u` – real number

## Output
* one Hit-and-Run step from `x` along `d`, the uniform draw on the chord given by `u`

## References

* [1] R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed
      Over Bounded Regions". Operations Research, 1984.
* [2] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One Hit-and-Run step from `x` along `d`, the uniform draw on the chord given by `u`. -/
noncomputable def HPolytope.hitAndRunStep (P : HPolytope α) (x d : α) (u : ℝ) : Option α :=
  -- the line set `L`: the Boundary Oracle's segment `[t̲, t̄]`
  (P.chordLow x d).bind fun tLow =>
    (P.chordHigh x d).map fun tHigh =>
      -- the point of `L` at fraction `u`
      x + (tLow + u * (tHigh - tLow)) • d

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
