module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A star set as a constrained zonotope

The coefficient box `[l, u]` is rescaled to `[-1, 1]`: `α_k = mid_k + rad_k β_k`, with
`mid = (l + u) / 2` and `rad = (u - l) / 2`. The center moves by `G · mid`, the generators are
scaled by `rad`, and the predicate is read at the rescaled factors with `HPolytope`'s own
operations: `translate` by `-mid`, then `comap` along `β ↦ rad ⊙ β`.

## Inputs
* `s` – halfspace-predicate star set

## Output
* constrained zonotope of the star set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.conZonotope (s : StarSet ℋ𝒫 n) : ConZonotope (Vec ℝ n) where
  h := s.m
  c := fun i => s.c i + ∑ k, s.G i k * ((s.dom.inf k + s.dom.sup k) / 2)
  G := fun k i => s.G i k * ((s.dom.sup k - s.dom.inf k) / 2)
  P := (s.pred.translate (-fun k => (s.dom.inf k + s.dom.sup k) / 2)).comap
    (LinearMap.pi fun k => ((s.dom.sup k - s.dom.inf k) / 2) • LinearMap.proj k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
