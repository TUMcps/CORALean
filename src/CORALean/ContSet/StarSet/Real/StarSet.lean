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
`P` on the coefficients, denoting `{c + G α | α ∈ P}`, with the coefficient box `[l, u]` of CORA's
star sets beside it: `{c + G α | α ∈ dom, α ∈ pred}`, `dom` a library `Interval`, so a star set is
bounded. The predicate is any family `P m` with a `ContSet` instance at `Vec ℝ m`: a `LevelSet`, a
`PolyLevelSet` (`ConPolyZono.starSet`), a `SupportFunction`, an `HPolytope`; a parameter of the
type, as the figure's arrows (`Conversion/`) are about. CORA's star set is `StarSet ℋ𝒫`:
`neuralNetwork` converts a `conZonotope` to `(c, G, C, d, l, u)` and propagates it. At that
predicate the set is a bounded polytope, exactly a `ConZonotope` (`Conversion/`).

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". Computer Aided Verification, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      20-October-2026 (Tobias Ladner)


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
