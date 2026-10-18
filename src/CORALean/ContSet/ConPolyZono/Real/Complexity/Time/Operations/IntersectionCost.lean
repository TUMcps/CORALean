module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.intersectionCost`

Asserted, not proved: `intersection` runs `intersectionDep` on the two `dependent` sets.
`intersectionDep` builds `agreeRow`, which negates each of `cPZ₂`'s dependent
generators once per output coordinate, `n * (h₂ + qI₂)` negations, and `intersectionB`, which is
one subtraction per coordinate, `n`. Everything
else — `plusA`, `PolyZonotope.plusE`, `appendE` — lays a field out block-diagonally, which
computes nothing but writes every entry of the result.

The result, with `H` dependent generators and `P` factors in all, `n` more constraints and `Q`
constraint generators, is the center and `H` generators of `n` entries, the `P` by `H` exponent
matrix, the `(m₁ + m₂ + n)` by `Q` matrix `A`, the vector `b` and the `P` by `Q` matrix `R`.
The conversions write their own results (`dependentCost`).

`h₂ + qI₂` is the *dependent* count `intersectionDep` sees, which
`Complexity/Space/Theorems/IntersectionP.lean` states as the `h` `intersectionDep`'s second operand
carries.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.intersection` costs at `Vec ℝ n` on operands of `pᵢ` factors, `hᵢ`, `qIᵢ`
generators, `mᵢ` constraints over `qᵢ`: the conversions, the arithmetic and the result's writes. -/
def ConPolyZono.intersectionCost (n p₁ h₁ qI₁ m₁ q₁ p₂ h₂ qI₂ m₂ q₂ : ℕ) : Cost :=
  let H := h₁ + qI₁ + (h₂ + qI₂)
  let P := p₁ + qI₁ + (p₂ + qI₂)
  let M := m₁ + m₂ + n
  let Q := q₁ + q₂ + H
  ConPolyZono.dependentCost n p₁ h₁ qI₁ m₁ q₁ + ConPolyZono.dependentCost n p₂ h₂ qI₂ m₂ q₂ +
    ⟨n * (h₂ + qI₂) + n + (n * (1 + H) + P * H + M * Q + M + P * Q)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
