import CORALean.HybridDynamics.Definitions.Location
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Location.guardIntersectZonoGirard`: the Girard and Le Guernic guard enclosure

CORA's `guardIntersect_zonoGirard`: in each basis `B`, the reach sets `R_j` meeting the guard
`G = {x | x·n = γ}` are enclosed by a box `I` in the coordinates of `B`, and the boxes of all
bases form a zonotope bundle. For each column `ℓ` of `B`, the zonogon `Π_{n,ℓ}(R_j)` is cut with
the line `x = γ` ([1, Alg. 2]) and the `y`-range is `[m_ℓ, M_ℓ]`; the boxes of the `R_j` are joined.

[1, Alg. 3] and [1, Alg. 4] find `[m_ℓ, M_ℓ]` by scanning and bisecting the sorted generators.
Here the upper end is the Lagrangian dual of the same linear program: for every `μ`, a state `x`
of `Z = ⟨c; g₁, …⟩` with `x·n = γ` has `x·ℓ = x·(ℓ - μ n) + μγ`, at most
`(ℓ - μ n)·c + Σ |(ℓ - μ n)·gⱼ| + μγ`; the least over the slopes `μ = (gⱼ·ℓ)/(gⱼ·n)` and `μ = 0`
is returned. Linear-programming duality makes it the scan's number, but only the inequality
is proved (`guardIntersectZonoGirard_outer`).

Left out: `aux_tightenSet` (the guard's inequality constraints) and `aux_robustProjection`, which
pins a coordinate to `γ n_ind`, the hyperplane value only for `‖n‖ = 1` (see FINDINGS.md).

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3] and [1, Alg. 4]: the upper end of `{x·ℓ | x ∈ Z, x·nv = γ}`, by the dual at
its breakpoints. -/
noncomputable def Location.zonoGirardUpper (Z : Real.Zonotope (Vec ℝ n)) (nv : Vec ℝ n) (γ : ℝ)
    (ℓ : Vec ℝ n) : ℝ :=
  let dual : ℝ → ℝ := fun μ => (ℓ - μ • nv) ⬝ᵥ Z.c + ∑ j, |(ℓ - μ • nv) ⬝ᵥ Z.G j| + μ * γ
  let slopes : List ℝ := (List.finRange Z.h).filterMap fun j =>
    if Z.G j ⬝ᵥ nv = 0 then none else some ((Z.G j ⬝ᵥ ℓ) / (Z.G j ⬝ᵥ nv))
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
