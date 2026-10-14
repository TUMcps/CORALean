module

public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.quadBilinCost`

Asserted, not proved: `Operations/QuadBilin.lean` is
`(x, y) ↦ (xᵀQ₁y, …, xᵀQₘy)`, so one application at `Vec ℝ n` is, per output
coordinate, one matrix-vector product `Q k *ᵥ y` at `n × n` and one dot product
against `x` — `n` multiplications and `n - 1` additions, rounded up to `2 * n`.

Its own file because `bilinCost` takes the cost of one application as an
argument, so this is what `quadMapDepCost` passes and the only thing separating
a quadratic map's count from a coordinatewise product's.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What one application of `PolyZonotope.quadBilin` costs at `m` matrices of
size `n × n`: a matrix-vector product and a dot product per coordinate. -/
def PolyZonotope.quadBilinCost (m n : ℕ) : Cost := m • (Cost.matVec n n + ⟨2 * n⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
