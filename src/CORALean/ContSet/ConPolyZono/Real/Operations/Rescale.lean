module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.rescale`

CORA's `@conPolyZono/rescale`: contract the factor box `[-1,1]ᵖ` against the constraint `A μ(α) =
b` with `contractPoly`, and re-parametrize every factor onto the contracted box, by `getSubset`.
The set is unchanged; only the factors' ranges are smaller, so a later enclosure is tighter.

`contractPoly` is a contractor [1, Def. 6], taken here as a parameter. CORA's `getSubset` takes
all factors at once; here the single-factor one is applied to factors `0, …, p-1` in turn. An
empty contracted box throws `CORA:emptySet` in CORA; the theorem assumes it is not.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `contract` – contractor on the factor box

## Output
* set rescaled to the contracted factor box

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contract` is CORA's `contractPoly` at the constraint `A μ(α) = b`. -/
noncomputable def ConPolyZono.rescale (cPZ : ConPolyZono α)
    (contract : Interval (Vec ℝ cPZ.p) → Interval (Vec ℝ cPZ.p)) : ConPolyZono α :=
  let dom := Interval.unit cPZ.p
  -- `if ~isempty(cPZ.cons.A)`
  let dom' := if cPZ.cons.m = 0 ∨ cPZ.cons.q = 0 then dom else contract dom
  let cen : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom'.inf ⟨r, h⟩ + dom'.sup ⟨r, h⟩) / 2 else 0
  let rad : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom'.sup ⟨r, h⟩ - dom'.inf ⟨r, h⟩) / 2 else 0
  (List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
