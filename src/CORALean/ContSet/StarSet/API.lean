module

public import CORALean.ContSet.StarSet.Real.API
public import CORALean.ContSet.StarSet.Float.API

/-!
# Star sets

The generalized star set `{c + G α | α ∈ P}` of Duggirala and Viswanathan with CORA's coefficient
box always beside it, `{c + G α | α ∈ [l, u], α ∈ P}`: a center, a basis, a box and a predicate on
the coefficients that is any representation in coefficient space, so a star set is as general as its
predicate, and bounded; with a `LevelSet` predicate star sets and bounded level sets denote the same
sets (`Conversion/`). CORA's neural-network evaluation uses an `HPolytope` predicate, `C α ≤ d`, at
which a star set is a bounded polytope, exactly what a `ConZonotope` denotes; what it adds is the
form a network layer steps through, a factor appended with its rows by the polytope's own
operations. Over ℝ at every predicate, and over a floating-point scalar at CORA's: the float layer
stores the same fields in `𝕋` and an error box, and an operation pays its rounding into it.-/
