module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Star sets: the representation

The generalized star set of [1, Def. 1]: a center `c`, a basis `G` of `m` vectors and a predicate
`P` on the coefficients, denoting `{c + G α | α ∈ P}`. The predicate is one of CORALean's own
representations in coefficient space, any family `P m` with a `ContSet` instance at `Vec ℝ m`: a
`LevelSet` for an arbitrary predicate, a `SupportFunction`, an `HPolytope`, an `Interval` for a box.
Which family is a parameter of the type, so a star set is as general as its predicate, and the
figure's arrows into and out of star sets (`Conversion/`) are about this class.

CORA's star set is `LinPred`: its `neuralNetwork` converts a `conZonotope` to `(c, G, C, d, l, u)`
(`nnHelper.conversionConZonoStarSet`) and propagates it, the predicate `C α ≤ d, l ≤ α ≤ u`. That
is an `HPolytope` cut by an `Interval` (`Conversion/`), kept as CORA keeps it: the rows as a list
read row by row, so a layer that adds a factor appends rows, and the box beside them, which bounds a
neuron (`rowBounds`) and which a float step relies on where it drops a row. At that predicate the
set is a bounded polytope, exactly a `ConZonotope` (`Conversion/`). The generators are stored
row-wise (`G i k` is the `i`-th coordinate of the `k`-th generator), as the layers read them.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1]: a center `c`, `m` generators `G` and a predicate `pred` on the coefficients,
drawn from the family `P` of coefficient-space representations. -/
structure StarSet (P : ℕ → Type) (n : ℕ) where
  m : ℕ
  c : Vec ℝ n
  G : Fin n → Fin m → ℝ
  pred : P m

/-- The points `c + G α` over the coefficients `α` the predicate holds of. -/
def StarSet.construct {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ} (s : StarSet P n) :
    Set (Vec ℝ n) :=
  {x | ∃ α : Fin s.m → ℝ, α ∈ ContSet.construct s.pred ∧ ∀ i, x i = s.c i + ∑ k, s.G i k * α k}

/-- CORA's predicate `C α ≤ d, l ≤ α ≤ u` on `m` coefficients: the rows `(a, b)`, `a · α ≤ b`,
which are `C` and `d` read row by row, and the box `[l, u]`. -/
structure StarSet.LinPred (m : ℕ) where
  cons : List ((Fin m → ℝ) × ℝ)
  l : Fin m → ℝ
  u : Fin m → ℝ

/-- The coefficients in the box `[l, u]` with every row satisfied. -/
def StarSet.LinPred.construct {m : ℕ} (p : StarSet.LinPred m) : Set (Vec ℝ m) :=
  {α | (∀ k, p.l k ≤ α k ∧ α k ≤ p.u k) ∧ ∀ r ∈ p.cons, ∑ k, r.1 k * α k ≤ r.2}

/-- What the predicate denotes, here beside it because a star set is stated with it. -/
instance {m : ℕ} : ContSet (StarSet.LinPred m) (Vec ℝ m) := ⟨StarSet.LinPred.construct⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
