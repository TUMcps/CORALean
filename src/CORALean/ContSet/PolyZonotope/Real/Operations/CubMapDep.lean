module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubPair
public import CORALean.ContSet.PolyZonotope.Real.Operations.CubQuad
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

@[expose] public section

/-!
# `PolyZonotope.cubMapDepOn`

CORA's `@polyZonotope/cubMap` on a set whose coefficients are all dependent: the cubic map
`{ (xᵀ T x) * x | x ∈ pZ }` of a polynomial zonotope is a polynomial zonotope again, exactly,
for the reason `quadMap` is: the factors are shared, so `mᵢ mⱼ mₖ` is a monomial, in the
exponent column `Eᵢ + Eⱼ + Eₖ`.

CORA's `aux_cubMapSingle` extends the generators by the center, builds the exponents of the
pairs `(a ≤ b)` and of the triples `(j; a ≤ b)`, and the generators of the pairs (`quadMat` with
both orders added) times the `k`-th entry of the `j`-th extended column, summed over `k`. Here
the pairs are all the ordered ones (as in `quadMap`: the same polynomial, symmetrization and
`removeRedundantExponents` not modelled), and the two steps are two `bilin`s: the quadratic forms
`w(i, k) = xᵀ T{i,k} x` over the factors, then `zᵢ = Σₖ xₖ w(i, k)`. The three arguments are
read out of one set `P` by linear maps: the identity three times is the single form, the
projections of a product the mixed form.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cubic map of the arguments `π₁ x, π₂ x, π₃ x` of the points `x` of `P`; sound only where
every coefficient is dependent. -/
def PolyZonotope.cubMapDepOn (π₁ π₂ π₃ : V →ₗ[ℝ] Vec ℝ n) (T : Fin m → Fin n → Mat ℝ n n)
    (P : PolyZonotope V) : PolyZonotope (Vec ℝ m) :=
  -- the quadratic forms `w(i, k) = (π₁ x)ᵀ T{i,k} (π₂ x)`
  let w : PolyZonotope (Vec ℝ (m * n)) :=
    PolyZonotope.bilin ((PolyZonotope.quadBilin (PolyZonotope.cubQuad T)).compl₁₂ π₁ π₂) P P rfl
  -- `Σₖ (π₃ x)ₖ w(i, k)`
  PolyZonotope.bilin ((PolyZonotope.cubPair m n).compl₁₂ π₃ LinearMap.id) P w rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
