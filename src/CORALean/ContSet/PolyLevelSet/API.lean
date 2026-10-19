module

public import CORALean.ContSet.PolyLevelSet.Real.API
public import CORALean.ContSet.PolyLevelSet.Float.API

/-!
# Polynomial level sets

A `LevelSet` whose function is a polynomial, stored by its coefficients, its exponent matrix, its
right-hand side and one comparison per row: `{x | (A μ_R(x) - b)ᵢ ⋈ᵢ 0}`. It is what a
constrained polynomial zonotope's factors satisfy, with `=` in every row (`ConPolyZono.cons`), and
it is a star set's predicate as any coefficient-space representation is
(`ConPolyZono.starSet`). `PolyLevelSet.levelSet` (`Conversion/`) reads it as a level set, with
the same set. The float layer stores `A` and `b` in `𝕋` with a slack `b_error` per row, as a
float constrained polynomial zonotope's constraint does.
-/
