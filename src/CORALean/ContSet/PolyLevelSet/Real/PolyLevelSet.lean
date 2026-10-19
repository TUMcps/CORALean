module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Polynomial level sets: the representation

A `LevelSet` whose function is a polynomial, stored by its data: the points `x` with
`(A μ_R(x))ᵢ - bᵢ ⋈ᵢ 0` in every row, `μ_R(x)` the monomials `∏ₖ xₖ^{R[k,j]}` read off the
exponent matrix `R`, `A` the coefficients of each row on those monomials and `⋈ᵢ ∈ {≤, <, =}`.
At `=` in every row this is the constraint `Σⱼ (∏ₖ αₖ^{R[k,j]}) A_(·,j) = b` of [1, Def. 5],
taken as a set of its own; [1, Def. 7]'s `constrDom` is it cut down to `[-1,1]ᵖ`. That is what a
constrained polynomial zonotope's factors satisfy (`ConPolyZono.cons`), as a constrained zonotope's
satisfy an `HPolytope`. The rows `≤` and `<` are [2, Eq. 2]'s invariants, at a polynomial `s`.

CORA has no class for it: its `levelSet` stores the symbolic equation, which a polynomial is one
kind of. `PolyLevelSet.levelSet` (`Conversion/`) is that reading, with the same set, so whatever is
proved of a `LevelSet` holds here; the stored data are what an operation can compute with.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
* [2] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


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

/-- The value of every constraint at `x`, `A μ_R(x) - b`: what each operator compares with `0`. -/
def PolyLevelSet.eval (P : PolyLevelSet n) (x : Vec ℝ n) : Vec ℝ P.m :=
  P.A *ᵥ PolyZonotope.monomial P.R x - P.b

/-- The points meeting every constraint `(A μ_R(x) - b)ᵢ ⋈ᵢ 0`. -/
def PolyLevelSet.construct (P : PolyLevelSet n) : Set (Vec ℝ n) :=
  {x | ∀ i, (P.op i).holds (P.eval x i)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
