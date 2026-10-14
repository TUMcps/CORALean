module

public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaPoint
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# `Capsule.vertices`

CORA's `@capsule/vertices_` for a planar capsule. A capsule has no vertices, so CORA returns
sampled points of its boundary: 500 points on each half circle, equally spaced in the angle, the
first half circle around `c + g` over `[θ - π/2, θ + π/2]` and the second around `c - g` over
`[θ + π/2, θ + 3π/2]`, with `θ` the angle of `g` (`0` for `g = 0`), and the first point repeated
at the end to close the polygon; a point capsule returns its centre. The point test
`representsa_(C,'point',1e-8)` is at tolerance `0` here (`Capsule.representsa_point`). The points
are on the boundary, not vertices: `Capsule.vertices_mem_frontier`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Classical


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule/vertices_` (planar): the sampled boundary points, `1001` of them, or the centre of a
point capsule. -/
noncomputable def Capsule.vertices (C : Capsule 2) : List (Vec ℝ 2) :=
  if C.representsa_point then [C.c] else
    let θ : ℝ := Complex.arg ⟨C.g 0, C.g 1⟩                       -- generatorAngle
    let arc : Vec ℝ 2 → ℝ → Fin 500 → Vec ℝ 2 := fun ctr a₀ i =>  -- 500 points, `linspace`
      let a : ℝ := a₀ + (i : ℝ) * (Real.pi / 499)
      ![ctr 0 + C.r * Real.cos a, ctr 1 + C.r * Real.sin a]
    let half₁ := List.ofFn (arc (C.c + C.g) (θ - Real.pi / 2))     -- around c + g
    let half₂ := List.ofFn (arc (C.c - C.g) (θ + Real.pi / 2))     -- around c - g
    half₁ ++ half₂ ++ [arc (C.c + C.g) (θ - Real.pi / 2) 0]        -- closed

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
