module

public import CORALean.Specification.STLInterval.Definitions.WithinTol

@[expose] public section

/-!
# `contains_` of an STL interval

`@stlInterval/contains_.m`, the `stlInterval` branch: both bounds included, an equal bound only if
the container's end is closed or the contained one open. An empty container contains only the empty
interval; `contains_` itself errors on an empty `S` over a nonempty container, `contains` (the
`catch` of `@contSet/contains.m`) answers `true`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.contains_ (tol : ℝ) : STLInterval → STLInterval → Prop
  | .empty, S => S = .empty
  | .nonempty .., .empty => True
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let upperIncluded := u₁ > u₂ ∨ (withinTol tol u₁ u₂ ∧ (rc₁ = true ∨ rc₂ = false))
    let lowerIncluded := l₁ < l₂ ∨ (withinTol tol l₁ l₂ ∧ (lc₁ = true ∨ lc₂ = false))
    lowerIncluded ∧ upperIncluded

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
