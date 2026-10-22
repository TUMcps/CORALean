module

public import CORALean.ContSet.InflatedContSet.Interfaces
public import CORALean.ContSet.StarSet.Real.Instances
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Star sets over a floating-point scalar: the representation

`Real.StarSet` at CORA's predicate, its numbers stored in `𝕋`: the tuple `(c, G, C, d, l, u)` of
CORA's `conversionConZonoStarSet`, the coefficient box `dom` the `[l, u]`, the predicate `pred` a
float `HPolytope` holding `C α ≤ d`, and the error box that makes it an `InflatedContSet`. Only that
predicate has a float form: a predicate of another family (a `LevelSet`, a `SupportFunction`) stores
functions, not numbers. The rounding of an operation is paid into `I_error` or into the predicate's
row slacks. What the stored numbers describe is `nominal`, the same tuple read as reals, the
predicate by its nominal part, slacks included, as `ConZonotope.P` is. The generalized star set of
[1, Def. 1] at that predicate; see `Real.StarSet`.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic
open scoped CORALean.Real

variable {𝕋 : Type} {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A star set stored in `𝕋`: `m` factors, center `c`, generators `G`, the coefficient box, the
predicate on the factors, and the box of what rounding has cost. -/
structure StarSet (𝕋 : Type) (n : ℕ) where
  m : ℕ
  c : Vec 𝕋 n
  G : Fin n → Fin m → 𝕋
  dom : Interval (Vec 𝕋 m)
  pred : HPolytope 𝕋 (Vec 𝕋 m)
  I_error : Interval (Vec 𝕋 n)

/-- The exact star set the stored floats describe, the predicate by its nominal part. -/
protected abbrev StarSet.nominal [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (s : StarSet 𝕋 n) :
    CORALean.Real.StarSet ℋ𝒫 n :=
  ⟨s.m, fun i => toReal (s.c i), fun i k => toReal (s.G i k), s.dom.nominal, s.pred.nominal⟩

/-- A float star set inflates the real one its stored floats describe, the `nominal` one. -/
instance [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (StarSet 𝕋 n) (CORALean.Real.StarSet ℋ𝒫 n)
      (Vec 𝕋 n) (Vec ℝ n) where
  nominal := StarSet.nominal
  I_error s := s.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev StarSet.construct [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (s : StarSet 𝕋 n) :
    Set (Vec ℝ n) :=
  InflatedContSet.construct s

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
