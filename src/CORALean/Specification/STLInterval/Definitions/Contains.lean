module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol

@[expose] public section

/-!
# `contains_` of an STL interval

`@stlInterval/contains_.m`, the `stlInterval` branch: both bounds included, an equal bound only if
the container's end is closed or the contained one open. An empty container contains only the empty
interval; `contains_` itself errors on an empty `S` over a nonempty container, `contains` (the
`catch` of `@contSet/contains.m`) answers `true`.

## Inputs
* `tol` – tolerance

## Output
* the first interval contains the second up to the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.contains_ (tol : ℝ) : STLInterval 𝕋 → STLInterval 𝕋 → Prop
  | .empty, S => S = .empty
  | .nonempty .., .empty => True
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let upperIncluded := toEReal u₁ > toEReal u₂ ∨
      (IsWithinTol tol (toEReal u₁) (toEReal u₂) ∧ (rc₁ = true ∨ rc₂ = false))
    let lowerIncluded := ((toReal l₁ : ℝ) : EReal) < (toReal l₂ : ℝ) ∨
      (IsWithinTol tol (toReal l₁ : ℝ) (toReal l₂ : ℝ) ∧ (lc₁ = true ∨ lc₂ = false))
    lowerIncluded ∧ upperIncluded

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
