module

public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Location.guardIntersectZonoGirard`: the Girard and Le Guernic guard enclosure

CORA's `guardIntersect_zonoGirard`: in each basis `B`, the reach sets meeting the guard
`G = {x | x·n = γ}` are enclosed by a box in the coordinates of `B`, and the boxes of all bases
form a zonotope bundle. The `y`-range `[m_ℓ, M_ℓ]` of [1, Alg. 3, 4] is found there by scanning the
sorted generators; here the upper end is the Lagrangian dual of the same linear program, the least
over the slopes `μ = (gⱼ·ℓ)/(gⱼ·n)` and `μ = 0`. Only the inequality is proved
(`guardIntersectZonoGirard_outer`). Left out: `aux_tightenSet` and `aux_robustProjection`, which
pins a coordinate to `γ n_ind` (see `references/coverage/hybridDynamics/location.md`, row
`guardIntersect_zonoGirard`).

## Inputs
* `Z` – zonotope
* `nv` – guard normal
* `γ` – guard offset
* `ℓ` – direction of the basis column

## Output
* upper end of the range along the direction

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] and [1, Alg. 4]: the upper end of `{x·ℓ | x ∈ Z, x·nv = γ}`, by the dual at
its breakpoints. -/
noncomputable def Location.zonoGirardUpper (Z : Real.Zonotope (Vec ℝ n)) (nv : Vec ℝ n) (γ : ℝ)
    (ℓ : Vec ℝ n) : ℝ :=
  -- 1. the dual bound `(ℓ - μ n)·c + Σ |(ℓ - μ n)·gⱼ| + μγ`, valid for every slope `μ`
  let dual : ℝ → ℝ := fun μ => (ℓ - μ • nv) ⬝ᵥ Z.c + ∑ j, |(ℓ - μ • nv) ⬝ᵥ Z.G j| + μ * γ
  -- 2. the breakpoints `μ = (gⱼ·ℓ)/(gⱼ·n)` of the sorted generators, those with `gⱼ·n ≠ 0`
  let slopes : List ℝ := (List.finRange Z.h).filterMap fun j =>
    if Z.G j ⬝ᵥ nv = 0 then none else some ((Z.G j ⬝ᵥ ℓ) / (Z.G j ⬝ᵥ nv))
  -- 3. the least dual bound over the breakpoints and `μ = 0`: the upper end `M_ℓ`
  slopes.foldl (fun m μ => min m (dual μ)) (dual 0)

/-- The set the bases `Bs` enclose the intersection of the reach sets `R₀ :: Rs` with
`{x | x·nv = γ}` by: `⋂ᵢ Bᵢ box(Iᵢ)`, `Iᵢ` the hull of the per-set cuts along the columns of
`Bᵢ`. -/
noncomputable def Location.guardIntersectZonoGirard (Bs : List (Mat ℝ n n))
    (R₀ : Real.Zonotope (Vec ℝ n)) (Rs : List (Real.Zonotope (Vec ℝ n))) (nv : Vec ℝ n)
    (γ : ℝ) : Set (Vec ℝ n) :=
  -- the cut of one reach set along `ℓ`: the lower end is the upper end in the direction `-ℓ`
  let upper : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => Location.zonoGirardUpper Z nv γ ℓ
  let lower : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => -upper Z (-ℓ)
  -- the hull over the reach sets
  let lb : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => min m (lower Z ℓ)) (lower R₀ ℓ)
  let ub : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => max m (upper Z ℓ)) (upper R₀ ℓ)
  -- the box `I` of basis `i`, mapped back by the basis
  ⋂ i : Fin Bs.length,
    (fun y => Bs[i] *ᵥ y) '' {y | ∀ k, lb (Bs[i]ᵀ k) ≤ y k ∧ y k ≤ ub (Bs[i]ᵀ k)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
