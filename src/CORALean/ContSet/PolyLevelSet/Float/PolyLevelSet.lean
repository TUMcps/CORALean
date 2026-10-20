module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.LevelSet.Real.Definitions.IsMetWithin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Polynomial level sets over a floating-point scalar: the representation

The rows `(A μ_R(x) - b)ᵢ ⋈ᵢ 0` of [1, Def. 5]'s constraint and of `Real.PolyLevelSet`, on the
domain box `dom`, with `A`, `b` and the box stored in `𝕋` and read back exactly (`nominalCore`),
plus the slack each row records: row `i` holds to within `|b_errorᵢ|` (`CompOp.IsMetWithin`).

There is no `I_error` and no `absorbRounding`: every operation rounds the rows' coefficients, which
the slack records, and none moves a point; an equation has no interior to take its slack back into
`b`. `relax` turns each row's slack into a variable, which a constrained polynomial zonotope can
afford as a factor (`ConPolyZono.absorbRounding`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `m` polynomial constraints on `n` variables over `q` monomials, each with its slack. -/
structure PolyLevelSet (𝕋 : Type) (n : ℕ) where
  /-- The constraints. -/
  m : ℕ
  /-- The monomials. -/
  q : ℕ
  /-- The coefficients of each constraint on the monomials. -/
  A : Mat 𝕋 m q
  /-- The exponent matrix: monomial `j` is `∏ₖ xₖ^{R[k,j]}`. -/
  R : Fin n → Fin q → ℕ
  /-- The right-hand side. -/
  b : Vec 𝕋 m
  /-- The slack of each row, read through `|·|`: row `i` holds to within `|b_errorᵢ|`. -/
  b_error : Vec 𝕋 m
  /-- The comparison of each constraint with `0`. -/
  op : Fin m → Real.CompOp
  /-- The domain box the variables range over. -/
  dom : Interval (Vec 𝕋 n)

/-- The rows and the box the stored floats state, read back exactly, the slack aside. -/
protected abbrev PolyLevelSet.nominalCore [SoundFloatArithmetic 𝕋] (P : PolyLevelSet 𝕋 n) :
    Real.PolyLevelSet n :=
  ⟨P.m, P.q, toRealMat P.A, P.R, toRealVec P.b, P.op, P.dom.nominal⟩

/-- The points of the box meeting every row of `nominalCore` to within its slack. -/
def PolyLevelSet.construct [SoundFloatArithmetic 𝕋] (P : PolyLevelSet 𝕋 n) : Set (Vec ℝ n) :=
  {x | x ∈ P.dom.construct
    ∧ ∀ i, (P.op i).IsMetWithin (P.nominalCore.eval x i) |toReal (P.b_error i)|}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
