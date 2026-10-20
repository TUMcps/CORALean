module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Polynomial level sets: the representation

A `LevelSet` whose function is a polynomial, over a domain box, stored by its data: the points `x`
of the box `dom` with `(A μ_R(x))ᵢ - bᵢ ⋈ᵢ 0` in every row, `μ_R(x)` the monomials `∏ₖ xₖ^{R[k,j]}`
read off the exponent matrix `R`, and `⋈ᵢ ∈ {≤, <, =}`. At `=` in every row and the box `[-1, 1]ᵖ`
this is [1, Def. 7]'s `constrDom`, the constraint of [1, Def. 5] on the factors' domain: what a
constrained polynomial zonotope's factors satisfy (`ConPolyZono.cons`, whose `cons_dom` fixes the
box). The rows `≤` and `<` are [2, Eq. 2]'s invariants, at a polynomial `s`. CORA has no class for
it; `PolyLevelSet.levelSet` (`Conversion/`) is that reading, the box written as `2n` rows, with the
same set, so whatever is proved of a `LevelSet` holds here.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
* [2] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `m` polynomial constraints on `n` variables over `q` monomials. -/
structure PolyLevelSet (n : ℕ) where
  /-- The constraints. -/
  m : ℕ
  /-- The monomials. -/
  q : ℕ
  /-- The coefficients of each constraint on the monomials. -/
  A : Mat ℝ m q
  /-- The exponent matrix: monomial `j` is `∏ₖ xₖ^{R[k,j]}`. -/
  R : Fin n → Fin q → ℕ
  /-- The right-hand side. -/
  b : Vec ℝ m
  /-- The comparison of each constraint with `0`. -/
  op : Fin m → CompOp
  /-- The domain box the variables range over. -/
  dom : Interval (Vec ℝ n)

/-- The value of every constraint at `x`, `A μ_R(x) - b`: what each operator compares with `0`. -/
def PolyLevelSet.eval (P : PolyLevelSet n) (x : Vec ℝ n) : Vec ℝ P.m :=
  P.A *ᵥ PolyZonotope.monomial P.R x - P.b

/-- The points of the box meeting every constraint `(A μ_R(x) - b)ᵢ ⋈ᵢ 0`. -/
def PolyLevelSet.construct (P : PolyLevelSet n) : Set (Vec ℝ n) :=
  {x | x ∈ P.dom.construct ∧ ∀ i, (P.op i).holds (P.eval x i)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
