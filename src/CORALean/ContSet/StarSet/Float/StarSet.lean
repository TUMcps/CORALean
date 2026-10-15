module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.StarSet.Real.Instances
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Star sets over a floating-point scalar: the representation

`Real.StarSet` with its numbers stored in the scalar `𝕋`: the tuple `(c, G, C, d, l, u)` of
CORA's `conversionConZonoStarSet`, the constraints kept as a list of rows `(a, b)`, `a · α ≤ b`,
and the error box that makes it an `InflatedContSet`.

The rounding of an operation is paid into `I_error`, a box in the ambient space, the one rule
every float representation here follows: the factors, the rows and the generators have no slack of
their own, so paying into them would change the shape of the set. What the stored numbers
describe is `nominal`, the same tuple read as reals; what the set denotes is the points of the
nominal star set, each moved by a point of the box.

The star set is the generalized star set of [1, Def. 1]; see `Real.StarSet`.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A star set stored in `𝕋`: `m` factors, centre `c`, generators `G`, constraint rows, the box
`[l, u]` of the factors, and the box of what rounding has cost. -/
structure StarSet (𝕋 : Type) (n : ℕ) where
  m : ℕ
  c : Vec 𝕋 n
  G : Fin n → Fin m → 𝕋
  cons : List ((Fin m → 𝕋) × 𝕋)
  l : Fin m → 𝕋
  u : Fin m → 𝕋
  I_error : Interval (Vec 𝕋 n)

/-- The exact star set the stored floats describe. -/
protected abbrev StarSet.nominal [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (s : StarSet 𝕋 n) :
    CORALean.Real.StarSet n :=
  ⟨s.m, fun i => toReal (s.c i), fun i k => toReal (s.G i k),
    s.cons.map fun r => (fun k => toReal (r.1 k), toReal r.2),
    fun k => toReal (s.l k), fun k => toReal (s.u k)⟩

instance [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (StarSet 𝕋 n) (CORALean.Real.StarSet n) (Vec 𝕋 n) (Vec ℝ n) where
  nominal := StarSet.nominal
  I_error s := s.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev StarSet.construct [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (s : StarSet 𝕋 n) :
    Set (Vec ℝ n) :=
  InflatedContSet.construct s

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
