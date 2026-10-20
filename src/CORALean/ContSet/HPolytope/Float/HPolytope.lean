module

public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Halfspace descriptions over a floating-point scalar: the representation

CORA's `polytope` [1, Def. 2] with `isHRep` set, its matrices held in `𝕋`, plus three errors, each
where its rounding lives: `b_error` the slack of the inequality rows, `A x ≤ b + |b_error|`;
`be_error` that of the equality rows, `|Aₑ x - bₑ| ≤ |be_error|`; and the state-space box `I_error`.
A slack is a magnitude, since rounding only widens a row. The nominal part is the exact polytope the
stored floats describe, slacks included; `construct` adds the box. An operation that rounds a
right-hand side writes the rounding into that row's slack (`HPolytope.setRhs`, #218); one that
stacks rows moves the box into the slacks (`HPolytope.boxToSlack`); one that reads the rows folds
all three into them (`HPolytope.absorbRounding`).

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HPolytope (𝕋 α : Type) where
  m : ℕ
  A : Fin m → α
  b : Vec 𝕋 m
  me : ℕ
  Ae : Fin me → α
  be : Vec 𝕋 me
  /-- The slack of the inequality rows: row `i` holds `Aᵢ x ≤ bᵢ + |b_errorᵢ|`. -/
  b_error : Vec 𝕋 m
  /-- The slack of the equality rows: row `i` holds `|Aeᵢ x - beᵢ| ≤ |be_errorᵢ|`. -/
  be_error : Vec 𝕋 me
  /-- The error box: what rounding has cost in the state space. -/
  I_error : Interval α

/-- The exact polytope the stored floats describe, slacks included, read through `toRealMat`:
the inequalities at `b + |b_error|`, each equality as the slab `be ± |be_error|`. -/
def HPolytope.nominal [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    CORALean.Real.HPolytope (Vec ℝ n) :=
  (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b + |toRealVec P.b_error|)).intersection
    (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be - |toRealVec P.be_error|)
      (toRealVec P.be + |toRealVec P.be_error|))

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (HPolytope 𝕋 (Vec 𝕋 n)) (CORALean.Real.HPolytope (Vec ℝ n))
      (Vec 𝕋 n) (Vec ℝ n) where
  nominal := HPolytope.nominal
  I_error P := P.I_error

/-- Inherited from `InflatedContSet`: `nominal + I_error`. -/
abbrev HPolytope.construct [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
