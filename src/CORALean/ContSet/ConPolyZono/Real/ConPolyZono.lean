import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# Constrained polynomial zonotopes: the representation

CORA's `conPolyZono`, and [1, Def. 5]: a `PolyZonotope` whose factors additionally satisfy
polynomial constraints `A μ(α) ∈ b`, the constraint monomials read off `EC` over
the *same* factors as the generators. That sharing is the content of the
representation — a constraint and a generator are two readings of one
`PolyZonotope.monomial` — so the constraints are a matrix relation, not a polytope.

`b` is an `Interval` where [1] writes `A μ(α) = b`: an equality has no direction
to round in, so no float layer could compute a constraint at all; `Interval.point
b` gives it back. Of the five counts two are renamed against [1] to avoid
`PolyZonotope`'s: `m` counts constraints, `s` constraint generators. `holds`
states the constraint over the data, which an operation assembling one needs.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


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
  /-- The independent generators. -/
  q : ℕ
  /-- The constraints. -/
  m : ℕ
  /-- The constraint generators. -/
  s : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin q → α
  A : Mat ℝ m s
  /-- Interval-valued, so that a bound has a direction to be rounded in. -/
  b : Interval (Vec ℝ m)
  EC : Fin p → Fin s → ℕ

/-- The constraint `A μ(α) ∈ b`, one row at a time and over the data rather than
over a set, so an operation can name the constraints of the system it is still
assembling. -/
def ConPolyZono.holds {p m s : ℕ} (A : Mat ℝ m s) (b : Interval (Vec ℝ m))
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) : Prop :=
  ∀ i, b.inf i ≤ (A *ᵥ PolyZonotope.monomial EC a) i
        ∧ (A *ᵥ PolyZonotope.monomial EC a) i ≤ b.sup i

/-- What a set's own factors must satisfy. -/
def ConPolyZono.satisfies (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) : Prop :=
  ConPolyZono.holds cPZ.A cPZ.b cPZ.EC a

def ConPolyZono.construct (cPZ : ConPolyZono α) : Set α :=
  {x | ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ cPZ.satisfies a
        ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i + ∑ j, β j • cPZ.GI j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
