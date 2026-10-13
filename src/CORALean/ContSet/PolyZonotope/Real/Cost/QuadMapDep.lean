import CORALean.ContSet.PolyZonotope.Real.Cost.Bilin
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadBilin
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep

/-!
# `PolyZonotope.quadMapDepCost`

Asserted, not proved: `Operations/QuadMapDep.lean` is `bilin` at `quadBilin`
with one set paired with itself, so the count is `bilinCost` at
`quadBilinCost`, at `h₁ = h₂ = h`.

`(h+1)²` pairs, each `m` quadratic forms at `n × n`, is where a polynomial
zonotope's exactness under a quadratic map is paid for: `O(h² m n²)` against a
zonotope's linear pass, for a set a zonotope cannot represent at all. The
`compact` that `reduce` runs first is what stops the square compounding across
steps.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.quadMapDep` costs at `m` matrices of size `n × n` over
`p` factors and `h` dependent generators: one pairing per pair of columns. -/
def PolyZonotope.quadMapDepCost (m n p h : ℕ) : Cost :=
  PolyZonotope.bilinCost (PolyZonotope.quadBilinCost m n) p h h

/-- Monotone in the factor and generator counts, so bounds on the operand's
sizes give a bound on the cost. -/
theorem PolyZonotope.quadMapDepCost_mono {p p' h h' : ℕ} (m n : ℕ) (hp : p ≤ p') (hh : h ≤ h') :
    PolyZonotope.quadMapDepCost m n p h ≤ PolyZonotope.quadMapDepCost m n p' h' :=
  PolyZonotope.bilinCost_mono _ hp hh hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
