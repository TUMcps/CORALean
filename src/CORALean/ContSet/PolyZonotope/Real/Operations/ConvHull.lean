module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
public import CORALean.ContSet.PolyZonotope.Real.Operations.NoIndep
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb

@[expose] public section

/-!
# `PolyZonotope.convHull`

CORA's `@polyZonotope/convHull_` for a second set that is a polynomial zonotope
(`aux_convHullMult`):
the dependent parts of the two sets (`pZ1_`, `pZ2_`: the independent generators dropped) are each
paired with themselves by `linComb`, the two chord sets with each other, and the independent
generators of the result are the generators of `enclose(Z1, Z2)` for the zero-centred zonotopes of
the two independent blocks, which for those is `Zonotope.linComb`.

The result is the chords of chords. It contains both operands (`union_subset_convHull`) and is the
convex hull only where such combinations of two points per operand suffice (not in general in
dimension three and more, and CORA's documentation says "convex hull"). The one-argument call
`convHull_(pZ)` is `linComb(pZ, pZ)`, `PolyZonotope.linComb`; a second set of another class is
converted to a polynomial zonotope first, and an empty second set returns `pZ`, neither modelled.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.convHull (pZ₁ pZ₂ : PolyZonotope α) : PolyZonotope α :=
  -- pZ1_ = polyZonotope(pZ1.c, pZ1.G, [], pZ1.E, pZ1.id), and pZ2_ likewise
  let pZ₁' := pZ₁.noIndep
  let pZ₂' := pZ₂.noIndep
  -- pZ = linComb(linComb(pZ1_, pZ1_), linComb(pZ2_, pZ2_))
  let pZ := (pZ₁'.linComb pZ₁').linComb (pZ₂'.linComb pZ₂')
  -- Z1 = zonotope(c0, pZ1.GI), Z2 = zonotope(c0, S.GI)
  let Z₁ : Zonotope α := ⟨pZ₁.q, 0, pZ₁.GI⟩
  let Z₂ : Zonotope α := ⟨pZ₂.q, 0, pZ₂.GI⟩
  -- Z = enclose(Z1, Z2)
  let Z := Z₁.linComb Z₂
  -- pZ.GI = Z.G
  { pZ with q := Z.h, GI := Z.G }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
