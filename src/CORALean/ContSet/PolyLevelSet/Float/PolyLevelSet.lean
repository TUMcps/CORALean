module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.LevelSet.Real.Definitions.IsMetWithin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Polynomial level sets over a floating-point scalar: the representation

The rows `(A μ_R(x) - b)ᵢ ⋈ᵢ 0` of [1, Def. 5]'s constraint and of `Real.PolyLevelSet`, with `A`
and `b` stored in `𝕋` and read back exactly (`nominalCore`), plus the slack each row records for
its rounding: row `i` holds to within `|b_errorᵢ|` (`CompOp.IsMetWithin`), so an equation is
`|(A μ_R(x) - b)ᵢ| ≤ |b_errorᵢ|`, as a float `HPolytope` records its rows'. The slack is a field
of its own, separate from any box, because it is a constraint-space quantity, one number per row.
The exponent matrix `R` and the operators are exact data and stay as they are.

There is no `I_error` and no `absorbRounding`: the variables of a level set are free, so there is
no ambient point to hold a box, and an equation has no interior to take its slack back into `b`.
`relax` turns each row's slack into a variable of its own, at the cost of `m` more variables, which
a constrained polynomial zonotope can afford as factors (`ConPolyZono.absorbRounding`) and a level
set of fixed dimension cannot.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

/-- The rows the stored floats state, read back exactly, the slack aside. -/
protected abbrev PolyLevelSet.nominalCore [SoundFloatArithmetic 𝕋] (P : PolyLevelSet 𝕋 n) :
    Real.PolyLevelSet n :=
  ⟨P.m, P.q, toRealMat P.A, P.R, toRealVec P.b, P.op⟩

/-- The points meeting every row of `nominalCore` to within its slack. -/
def PolyLevelSet.construct [SoundFloatArithmetic 𝕋] (P : PolyLevelSet 𝕋 n) : Set (Vec ℝ n) :=
  {x | ∀ i, (P.op i).IsMetWithin (P.nominalCore.eval x i) |toReal (P.b_error i)|}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
