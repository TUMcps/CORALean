module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Constrained polynomial zonotopes: the representation

CORA's `conPolyZono`, and [1, Def. 5]: a `PolyZonotope` whose factors additionally satisfy
polynomial constraints `A μ_R(α) = b`, the constraint monomials read off the exponent matrix `R`
over the *same* factors as the generators — a constraint and a generator are two readings of one
`PolyZonotope.monomial`. The symbols are [1]'s: `p` factors, `h` generators, `m` constraints and
`q` constraint generators (`cons.m`, `cons.q`); [1] has no independent generators, their count is
`qI`, `PolyZonotope`'s `q` [2, Def. 1] being the letter [1] gives the constraint generators.

The constraint is the field `cons`, a `PolyLevelSet` on the factors, as a constrained zonotope's
is an `HPolytope`: an operation on it is one of `PolyLevelSet`'s (`and_`, `cartProd`, `padVars`,
`relax`, `compact`). Every row is an equation, as in CORA, and `cons_eq` says so: a `≤` row would
make a different set from [1]'s, and `union` rewrites each row with its selector factor
([1, Thm. 1]), which is sound for an equation only. The factors' box `[-1, 1]ᵖ` is the
constraint's own domain, which `cons_dom` fixes, so `cons` is [1, Def. 7]'s `constrDom` and
`construct` adds no box of its own. An operation keeps both invariants from its operands'.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
* [2] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure ConPolyZono (α : Type) where
  /-- The dependent factors, shared by the generators and the constraints. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators, `qI` of them; [1] has none. -/
  qI : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin qI → α
  /-- The constraint `A μ_R(α) = b` of [1] on the factors: `m` rows over `q` monomials. -/
  cons : PolyLevelSet p
  /-- Every constraint row is an equation, as in [1]. -/
  cons_eq : ∀ i, cons.op i = .eq
  /-- The factors range over the constraint's domain, the unit box, as in [1]. -/
  cons_dom : cons.dom = Interval.unit p

def ConPolyZono.construct (cPZ : ConPolyZono α) : Set α :=
  {x | ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ, (∀ j, |β j| ≤ 1) ∧ a ∈ cPZ.cons.construct
        ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i + ∑ j, β j • cPZ.GI j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
