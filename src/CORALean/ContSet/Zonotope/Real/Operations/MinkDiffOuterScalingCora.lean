import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Radius

/-!
# `Zonotope.minkDiffOuterScalingCora`, CORA's `minkDiff(Z, I, 'outer:scaling')`

CORA's `@zonotope/minkDiff.m` with method `'outer:scaling'` and an interval subtrahend `I`: the
subtrahend is turned into `zonotope(I)` (l. 104), and for a full-dimensional minuend outside
`n = 2` (where l. 120 forces `'exact'`) l. 148-150 call `aux_minkDiffOuterInterval` (l. 311-326).
That scales the minuend about its own centre by `1 - radSub ./ radMin` through `enlarge`
(`@contSet/enlarge.m`: `S - c`, `.* factor`, `+ c`) and never subtracts the subtrahend's centre.
One `let` per line of the source; the `representsa_` guard (l. 314) only throws.

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 99-104, 117-120, 148-150, 311-326.
* [2] `contSet/@contSet/enlarge.m`, CORA.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `'outer:scaling'` at an interval subtrahend: the minuend scaled coordinatewise about its
own centre by `1 - radSub ./ radMin`. -/
noncomputable def Zonotope.minkDiffOuterScalingCora (minuend : Zonotope (Vec ℝ n))
    (I : Interval (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  -- l. 104: `subtrahend = zonotope(subtrahend)`
  let subtrahend : Zonotope (Vec ℝ n) := I.zonotope
  -- l. 321: `radMin = rad(interval(minuend))`
  let radMin : Vec ℝ n := minuend.interval.radius
  -- l. 322: `radSub = rad(interval(subtrahend))`
  let radSub : Vec ℝ n := subtrahend.interval.radius
  -- l. 323: `scale = 1 - radSub./radMin`
  let scale : Vec ℝ n := fun i => 1 - radSub i / radMin i
  -- l. 324, `enlarge(minuend, scale)` [2]: `c = center(S)`
  let c : Vec ℝ n := minuend.c
  -- [2]: `S = S - c`
  let S₁ : Zonotope (Vec ℝ n) := ⟨minuend.h, minuend.c - c, minuend.G⟩
  -- [2]: `S = S .* factor`, i.e. `diag(factor) * S`
  let S₂ : Zonotope (Vec ℝ n) :=
    ⟨S₁.h, fun i => scale i * S₁.c i, fun j i => scale i * S₁.G j i⟩
  -- [2]: `S = S + c`
  ⟨S₂.h, S₂.c + c, S₂.G⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
