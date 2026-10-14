module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Interval.Real.Operations.Rdivide
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_times_`: the contraction of a product

`aux_times_(int,intPrev1,intPrev2)` of `syntaxTree.m`: from `x₁ x₂ ∈ int`, `x₁ ∈ int / intPrev2`
where
`0 ∉ intPrev2`, and the same for `x₂`; an operand whose interval contains `0` is left as it is. A
numeric
operand is a point interval, so `int / c` for a number `c ≠ 0`, and `intPrev2` for `c = 0` (CORA
divides
by `0` there, which `interval` leaves undefined).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_times_`: `intPrev1 & (int / intPrev2)` where `0 ∉ intPrev2`, and the same for `intPrev2`.
-/
noncomputable def SyntaxTree.funHanTimes (int prev₁ prev₂ : Dom) : Pair :=
  let res₁ := if prev₂.inf 0 ≤ 0 ∧ 0 ≤ prev₂.sup 0 then prev₁
    else Real.Interval.intersection prev₁ (Real.Interval.rdivide int prev₂)
  let res₂ := if prev₁.inf 0 ≤ 0 ∧ 0 ≤ prev₁.sup 0 then prev₂
    else Real.Interval.intersection prev₂ (Real.Interval.rdivide int prev₁)
  ⟨res₁, res₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
