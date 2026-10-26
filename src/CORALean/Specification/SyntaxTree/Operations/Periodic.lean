module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The periodic tail of `aux_sin_`, `aux_cos_` and `aux_tan_`

The three functions of `syntaxTree.m` differ only in the two inverse branches (`asin(int)` and
`-asin(int) + pi`, `acos(int)` and its negative, `atan(int)` and `atan(int) + pi`); the rest finds
the
largest and the smallest solution `x + 2 pi k` inside `intPrev` and meets `intPrev` with their hull.
`contains` is exact (`tol = 0`).

Real-only, a specification: it computes with real numbers exactly; its rounded refinement is
`SyntaxTree.periodicFloat`.

## Inputs
* `resTemp₁` – interval of the first branch
* `resTemp₂` – interval of the second branch
* `prev` – previous interval

## Output
* the interval of shifted branch solutions closest to the previous interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The solutions of the two inverse branches, shifted by `2 pi k`, closest to `intPrev`'s ends. -/
noncomputable def SyntaxTree.periodic (resTemp₁ resTemp₂ prev : Dom) : Dom :=
  let p := 2 * Real.pi
  -- compute updated upper bound
  let ind₁ : ℝ := ⌈(prev.sup 0 - resTemp₁.sup 0) / p⌉
  let ind₂ : ℝ := ⌈(prev.sup 0 - resTemp₂.sup 0) / p⌉
  let supNew :=
    if (resTemp₁.inf 0 + ind₁ * p ≤ prev.sup 0 ∧ prev.sup 0 ≤ resTemp₁.sup 0 + ind₁ * p) ∨
        (resTemp₂.inf 0 + ind₂ * p ≤ prev.sup 0 ∧ prev.sup 0 ≤ resTemp₂.sup 0 + ind₂ * p) then
      prev.sup 0
    else
      let diff₁ := prev.sup 0 - (resTemp₁.sup 0 + (ind₁ - 1) * p)
      let diff₂ := prev.sup 0 - (resTemp₂.sup 0 + (ind₂ - 1) * p)
      if diff₁ < diff₂ then resTemp₁.sup 0 + (ind₁ - 1) * p
      else resTemp₂.sup 0 + (ind₂ - 1) * p
  -- compute updated lower bound
  let ind₃ : ℝ := ⌊(prev.inf 0 - resTemp₁.inf 0) / p⌋
  let ind₄ : ℝ := ⌊(prev.inf 0 - resTemp₂.inf 0) / p⌋
  let infNew :=
    if (resTemp₁.inf 0 + ind₃ * p ≤ prev.inf 0 ∧ prev.inf 0 ≤ resTemp₁.sup 0 + ind₃ * p) ∨
        (resTemp₂.inf 0 + ind₄ * p ≤ prev.inf 0 ∧ prev.inf 0 ≤ resTemp₂.sup 0 + ind₄ * p) then
      prev.inf 0
    else
      let diff₁ := resTemp₁.inf 0 + (ind₃ + 1) * p - prev.inf 0
      let diff₂ := resTemp₂.inf 0 + (ind₄ + 1) * p - prev.inf 0
      if diff₁ < diff₂ then resTemp₁.inf 0 + (ind₃ + 1) * p
      else resTemp₂.inf 0 + (ind₄ + 1) * p
  -- intersect with previous value
  Real.Interval.intersection prev (interval infNew supNew)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
