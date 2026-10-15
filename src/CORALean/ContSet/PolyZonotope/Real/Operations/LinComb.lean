module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
public import CORALean.ContSet.Zonotope.Real.Operations.PairDiff
public import CORALean.ContSet.Zonotope.Real.Operations.PairSum

@[expose] public section

/-!
# `PolyZonotope.linComb`

CORA's `@polyZonotope/linComb`, and the operation the representation is good at:
one fresh dependent factor `α` carries the whole segment parameter. Writing
`λ = (1+α)/2` turns `λ y₁ + (1-λ) y₂` into `½(y₁+y₂) + ½α(y₁-y₂)`, and both
halves are again polynomial in the factors, so the dependent part loses nothing
where a zonotope has to spend a generator on the center difference.

Three dependent blocks come out of that: `½G₁ ++ ½G₂` at the original monomials,
`½G₁ ++ -½G₂` at the same monomials times `α`, and one generator `½(c₁-c₂)` at
`α` alone. `linCombE` repeats the block-diagonal `plusE` across the first two
blocks and sets the fresh factor's row to `1` on exactly the second.

The independent generators are where exactness stops: their coefficients come
out as `½(1±α)βⱼ`, which the representation cannot express, so the two blocks
are enclosed instead. That enclosure is CORA's `zonotope/enclose` at a zero
center, which is `Zonotope.pairSum` and `Zonotope.pairDiff` — tighter than
keeping each `GIⱼ` at full width, at the same count `q₁ + q₂`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.linComb (pZ₁ pZ₂ : PolyZonotope α) : PolyZonotope α where
  p := pZ₁.p + pZ₂.p + 1
  h := pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1)
  q := pZ₁.q + pZ₂.q
  c := (2:ℝ)⁻¹ • (pZ₁.c + pZ₂.c)
  G := Fin.append
        (Fin.append (fun i => (2:ℝ)⁻¹ • pZ₁.G i) (fun i => (2:ℝ)⁻¹ • pZ₂.G i))
        (Fin.append
          (Fin.append (fun i => (2:ℝ)⁻¹ • pZ₁.G i) (fun i => (-(2:ℝ)⁻¹ : ℝ) • pZ₂.G i))
          (fun _ : Fin 1 => (2:ℝ)⁻¹ • (pZ₁.c - pZ₂.c)))
  E := PolyZonotope.linCombE pZ₁.E pZ₂.E
  GI := Fin.append (Zonotope.pairSum pZ₁.GI pZ₂.GI) (Zonotope.pairDiff pZ₁.GI pZ₂.GI)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
