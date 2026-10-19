module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.BilinCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.quadMapDepCost`

Asserted, not proved: `Operations/QuadMapDep.lean` is `bilin` at `quadBilin`
with one set paired with itself, so the count is `bilinCost` at
`aux_quadBilinCost`, at `h₁ = h₂ = h`.

`(h+1)²` pairs, each `m` quadratic forms at `n × n`, is where a polynomial
zonotope's exactness under a quadratic map is paid for: `O(h² m n²)` against a
zonotope's linear pass, for a set a zonotope cannot represent at all. The
`compact` that `reduce` runs first is what stops the square compounding across
steps.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What one application of `PolyZonotope.quadBilin` costs at `m` matrices of size `n × n`: a
matrix-vector product, a dot product and the write of its value per coordinate. -/
def PolyZonotope.aux_quadBilinCost (m n : ℕ) : Cost := m • (Cost.matVec n n + ⟨2 * n + 1⟩)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.quadMapDep` costs at `m` matrices of size `n × n` over `p` factors and `h`
dependent generators: one pairing per pair of columns, into `Vec ℝ m`. -/
def PolyZonotope.quadMapDepCost (m n p h : ℕ) : Cost :=
  PolyZonotope.bilinCost (PolyZonotope.aux_quadBilinCost m n) m p h h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
