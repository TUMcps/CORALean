module

public import CORALean.ContSet.ConPolyZono.Real.Operations.RescaleStep
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.rescale`

CORA's `@conPolyZono/rescale`: contract the factor box `[-1,1]ᵖ` against the constraint
`A μ(α) = b` with `contractPoly`, and re-parametrize every factor onto the contracted
box, by `getSubset`. The set is unchanged; only the factors' ranges are smaller, so a
later enclosure is tighter.

`contractPoly` (forward-backward, linearization, polynomial or interval contraction, or all
of them) is a contractor [1, Def. 6]: it is taken here as a parameter, and what is proved
about `rescale` assumes the contractor contract and nothing else. CORA's `getSubset` takes
all factors at once; here the single-factor `getSubset` is applied to factors `0, …, p-1`
in turn, the same substitution. When the contracted box is empty CORA throws
`CORA:emptySet`; the theorem assumes it is not.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contract` is CORA's `contractPoly` at the constraint `A μ(α) = b`. -/
noncomputable def ConPolyZono.rescale (cPZ : ConPolyZono α)
    (contract : Interval (Vec ℝ cPZ.p) → Interval (Vec ℝ cPZ.p)) : ConPolyZono α :=
  let dom := ConPolyZono.unitBox cPZ.p
  -- `if ~isempty(cPZ.A)`
  let dom' := if cPZ.m = 0 ∨ cPZ.q = 0 then dom else contract dom
  let cen : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom'.inf ⟨r, h⟩ + dom'.sup ⟨r, h⟩) / 2 else 0
  let rad : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom'.sup ⟨r, h⟩ - dom'.inf ⟨r, h⟩) / 2 else 0
  (List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
