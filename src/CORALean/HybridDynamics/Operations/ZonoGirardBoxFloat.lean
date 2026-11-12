module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.HybridDynamics.Operations.ZonoGirardUpperFloat
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Location.zonoGirardBoxFloat`

The box of one basis in CORA's `guardIntersect_zonoGirard`: along each column `ℓ` of `B`, the cut
of a reach set by the guard `{x | x·n = γ}` is `[-U(-ℓ), U(ℓ)]`, `U` the dual bound
`Location.zonoGirardUpperFloat`, and the intervals of the reach sets `R₀ :: Rs` are joined. An
interval with `inf > sup` is an empty cut, which `Location.guardIntersectZonoGirardFloat` leaves
in place and `HybridAutomaton.reachQueueFloat` drops.

## Inputs
* `B` – basis
* `R₀` – initial zonotope
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset

## Output
* the joined box of the cuts, in the coordinates of `B`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The union of the cuts of `R₀ :: Rs` by the hyperplane, boxed along the columns of `B`. -/
def Location.zonoGirardBoxFloat (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋) : Interval (Vec 𝕋 n) :=
  -- the cut of one reach set along each column `ℓ` of `B`, `[-U(-ℓ), U(ℓ)]`
  let cut : Zonotope (Vec 𝕋 n) → Interval (Vec 𝕋 n) := fun R =>
    ⟨fun k => neg (Location.zonoGirardUpperFloat R nv γ (-(Bᵀ k))),
      fun k => Location.zonoGirardUpperFloat R nv γ (Bᵀ k)⟩
  (Rs.map cut).foldl Interval.or (cut R₀)                            -- the cuts, joined

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
