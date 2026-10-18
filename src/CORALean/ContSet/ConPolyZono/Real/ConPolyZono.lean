module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Constrained polynomial zonotopes: the representation

CORA's `conPolyZono`, and [1, Def. 5]: a `PolyZonotope` whose factors additionally satisfy
polynomial constraints `A μ_R(α) = b`, the constraint monomials read off the exponent
matrix `R` over the *same* factors as the generators. That sharing is the content of the
representation — a constraint and a generator are two readings of one
`PolyZonotope.monomial` — so the constraints are a matrix relation, not a polytope.

The symbols are [1]'s: `p` factors, `h` generators, `m` constraints, `q` constraint generators,
so `A` is `m × q` and `R` is `p × q`. [1] has no independent generators; their count is `qI`,
`PolyZonotope`'s `q` [2, Def. 1] being the letter [1] gives the constraint generators.

The constraint system is a `PolyLevelSet` on the factors with `=` in every row (`cons`), as a
constrained zonotope's is an `HPolytope`: `satisfies a` is `a ∈ cons.construct`
(`satisfies_iff_mem_cons`). `A`, `b` and `R` are stored as [1] writes them, `b` a point vector;
what rounding costs the float layer's rows is its own record, `b_error`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
* [2] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
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
  /-- The constraints. -/
  m : ℕ
  /-- The constraint generators. -/
  q : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin qI → α
  A : Mat ℝ m q
  /-- The constraint vector `b` of [1]. -/
  b : Vec ℝ m
  /-- The constraint exponent matrix, `R` of [1]. -/
  R : Fin p → Fin q → ℕ

/-- The constraint `A μ_R(α) = b`, one row at a time and over the data rather than over a set,
so an operation can name the constraints of the system it is still assembling. -/
def ConPolyZono.holds {p m q : ℕ} (A : Mat ℝ m q) (b : Vec ℝ m)
    (R : Fin p → Fin q → ℕ) (a : Fin p → ℝ) : Prop :=
  ∀ i, (A *ᵥ PolyZonotope.monomial R a) i = b i

/-- The constraint system as a polynomial level set on the factors, `=` in every row. -/
def ConPolyZono.cons (cPZ : ConPolyZono α) : PolyLevelSet cPZ.p :=
  ⟨cPZ.m, cPZ.q, cPZ.A, cPZ.R, cPZ.b, fun _ => .eq⟩

/-- What a set's own factors must satisfy: `holds` at its own fields. -/
def ConPolyZono.satisfies (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) : Prop :=
  ConPolyZono.holds cPZ.A cPZ.b cPZ.R a

def ConPolyZono.construct (cPZ : ConPolyZono α) : Set α :=
  {x | ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ cPZ.satisfies a
        ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i + ∑ j, β j • cPZ.GI j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
