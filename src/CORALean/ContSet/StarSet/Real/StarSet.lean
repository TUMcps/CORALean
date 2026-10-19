module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Star sets: the representation

The generalized star set of [1, Def. 1]: a center `c`, a basis `G` of `m` vectors and a predicate
`P` on the coefficients, denoting `{c + G α | α ∈ P}`, here with the coefficient box `[l, u]` of
CORA's star sets always beside it: the set is `{c + G α | α ∈ dom, α ∈ pred}`, `dom` a library
`Interval`, so a star set is bounded. The predicate is one of CORALean's own representations in
coefficient space, any family `P m` with a `ContSet` instance at `Vec ℝ m`: a `LevelSet` for an
arbitrary predicate, a `PolyLevelSet` for a polynomial one (a constrained polynomial zonotope's,
`ConPolyZono.starSet`), a `SupportFunction`, an `HPolytope`. Which family is a parameter of the
type, so a star set is as general as its predicate, and the figure's arrows into and out of star
sets (`Conversion/`) are about this class.

CORA's star set is the instance `StarSet ℋ𝒫`: its `neuralNetwork` converts a `conZonotope` to
`(c, G, C, d, l, u)` (`nnHelper.conversionConZonoStarSet`) and propagates it, the predicate the
polytope `C α ≤ d` and the box `[l, u]`, which bounds a neuron (`rowBounds`). A layer that adds a
factor appends a variable and rows through `HPolytope`'s own operations (`lift_`, `intersection`).
At that predicate the set is a bounded polytope, exactly a `ConZonotope` (`Conversion/`). `G i k`
is the `i`-th coordinate of the `k`-th generator, as the layers read them.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1]: a center `c`, `m` generators `G`, the coefficient box `dom` and a predicate `pred`
on the coefficients, drawn from the family `P` of coefficient-space representations. -/
structure StarSet (P : ℕ → Type) (n : ℕ) where
  m : ℕ
  c : Vec ℝ n
  G : Fin n → Fin m → ℝ
  /-- The coefficient box `[l, u]`. -/
  dom : Interval (Vec ℝ m)
  pred : P m

/-- The points `c + G α` over the coefficients `α` of the box the predicate holds of. -/
def StarSet.construct {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ} (s : StarSet P n) :
    Set (Vec ℝ n) :=
  {x | ∃ α : Fin s.m → ℝ, (α ∈ s.dom.construct ∧ α ∈ ContSet.construct s.pred)
    ∧ ∀ i, x i = s.c i + ∑ k, s.G i k * α k}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
