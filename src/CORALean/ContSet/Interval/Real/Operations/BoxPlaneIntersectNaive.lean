module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-!
# `Interval.boxPlaneIntersectNaive`

[1, Alg. 1], `Naive(B, α)`, CORA's `boxPlaneIntersectNaive`: every edge `e_uv` of the box, from
the vertex `v` to its neighbour `u` one coordinate up (a label `l` and a coordinate `j` with
`lⱼ` false), meets `Σᵢ xᵢ = α` at `t⋆ = (α - Σᵢ vᵢ)/Σᵢ(uᵢ - vᵢ)`, [1, Eq. 4], and contributes
`e_uv(t⋆)` when `0 ≤ t⋆ ≤ 1`. CORA's version scales the hyperplane by `β`; this is the paper's.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `L`, the cut points of the edges of `I` with `Σᵢ xᵢ = α`. -/
noncomputable def Interval.boxPlaneIntersectNaive (I : Interval (Vec ℝ n)) (α : ℝ) :
    Finset (Vec ℝ n) :=
  -- 2-3: the edges, a vertex label and the coordinate to raise
  (Finset.univ.filter fun e : (Fin n → Bool) × Fin n => e.1 e.2 = false).biUnion fun e =>
    let v := I.corner e.1
    let u := I.corner (Function.update e.1 e.2 true)
    let tStar := (α - ∑ i, v i) / ∑ i, (u i - v i)                   -- 4: Eq. 4
    if 0 ≤ tStar ∧ tStar ≤ 1 then {v + tStar • (u - v)} else ∅       -- 5-6

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
