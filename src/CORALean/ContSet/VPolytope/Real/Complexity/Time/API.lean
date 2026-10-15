module

public import CORALean.ContSet.VPolytope.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.VPolytope.Real.Complexity.Time.Theorems.API

/-!
# What running `VPolytope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/Space/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

`plus` pays `n * k₁ * k₂` for pairing and adding every vertex against every
other; `mtimes` a matrix-vector product per vertex; `linComb` nothing, its
vertex lists only concatenating.

`intersection` is **not** counted. It goes out to `HPolytope` — free there —
and comes back by `HPolytope.vPolytope`, whose own docstring reads `2^m`: an
exponential enumeration over subsets of rows, each candidate a linear solve
this model has no unit price for. A number here would guess at both the
exponent's base and the solve inside it. `mtimesMatPolytope` is left out for
the same reason one level down: it is `bilin`, and `bilin`'s own count is not
stated for any representation that carries it — `PolyZonotope.bilinCost`
takes what one pairing costs as a parameter precisely because this
representation, like that one, cannot fix it.

`map` and `point` are left out as `Zonotope`'s constructors are: `point` places
data, and `map`'s cost is a parameter no caller here supplies, `mtimes` being
`map` at the one map this file can price.
-/
