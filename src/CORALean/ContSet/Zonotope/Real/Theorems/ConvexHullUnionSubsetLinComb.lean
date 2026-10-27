module

public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# The convex hull of two zonotopes lies in their `linComb`

[1, Eq. 6]: `CH(Z₁, e^{Ar} Z₁) ⊆ ½(c₁ + e^{Ar}c₁, g⁽¹⁾ + e^{Ar}g⁽¹⁾, …, c₁ - e^{Ar}c₁,
g⁽¹⁾ - e^{Ar}g⁽¹⁾, …)`. That zonotope is `Zonotope.linComb Z₁ Z₂` at `Z₂ = e^{Ar} Z₁`: center
`½(c₁ + c₂)`, the paired columns `½(g⁽ʲ⁾ + e^{Ar}g⁽ʲ⁾)` and `½(g⁽ʲ⁾ - e^{Ar}g⁽ʲ⁾)` (the two
blocks have the same length), and the column `½(c₁ - c₂)`. Stated for any two zonotopes,
of which the paper's pair is one.

`linComb` holds both sets, `Z₁` at the end `λ = 1` of its segments and `Z₂` at `λ = 0`, and
is convex, so it holds their hull.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Hypotheses
* none

## Conclusion
* the hull of the union lies in the combination

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6]: `CH(Z₁ ∪ Z₂) ⊆ linComb Z₁ Z₂`, the paper's `Z₂ = e^{Ar} Z₁` included. -/
theorem Zonotope.convexHull_union_subset_linComb (Z₁ Z₂ : Zonotope α) : -- --- CONCL ---
    convexHull ℝ (Z₁.construct ∪ Z₂.construct)
      ⊆ (Z₁.linComb Z₂).construct := by -- --- PROOF ---
  refine convexHull_min (Set.union_subset ?_ ?_) (Zonotope.convex_construct _)
  -- `Z₁` is the end `λ = 1` of the segments to `Z₂`'s center
  · intro x hx
    refine Zonotope.linComb_outer Z₁ Z₂
      ⟨x, hx, Z₂.c, Zonotope.center_mem_construct Z₂, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp
  -- `Z₂` is the end `λ = 0` of the segments from `Z₁`'s center
  · intro x hx
    refine Zonotope.linComb_outer Z₁ Z₂
      ⟨Z₁.c, Zonotope.center_mem_construct Z₁, x, hx, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
