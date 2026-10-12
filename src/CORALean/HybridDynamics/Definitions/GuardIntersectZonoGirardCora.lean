import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirard
import CORALean.HybridDynamics.Definitions.RobustProjectionCora

/-!
# `Location.guardIntersectZonoGirardCora`: the guard enclosure with CORA's pinning

`Location.guardIntersectZonoGirard` with the step it leaves out: after the cuts of each basis `D`
are joined into `lb`, `ub`, they pass through `aux_robustProjection`
(`Location.robustProjectionCora`) before the box is formed, as CORA's `aux_enclosingInterval`
does. Everything else is as there (no `aux_tightenSet`, the dual bound for the cut).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of the reach sets `R₀ :: Rs` with `{x | x·nv = γ}` by the bases `Bs`, with the
pinning of `aux_robustProjection`. -/
noncomputable def Location.guardIntersectZonoGirardCora (Bs : List (Mat ℝ n n))
    (R₀ : Real.Zonotope (Vec ℝ n)) (Rs : List (Real.Zonotope (Vec ℝ n))) (nv : Vec ℝ n)
    (γ : ℝ) : Set (Vec ℝ n) :=
  let upper : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => Location.zonoGirardUpper Z nv γ ℓ
  let lower : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => -upper Z (-ℓ)
  let lb : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => min m (lower Z ℓ)) (lower R₀ ℓ)
  let ub : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => max m (upper Z ℓ)) (upper R₀ ℓ)
  ⋂ i : Fin Bs.length,
    -- `[lb, ub] = aux_robustProjection(B, n, gamma, lb, ub)`
    let lu := Location.robustProjectionCora Bs[i] nv γ (fun k => lb (Bs[i]ᵀ k))
      (fun k => ub (Bs[i]ᵀ k))
    (fun y => Bs[i] *ᵥ y) '' {y | ∀ k, lu.1 k ≤ y k ∧ y k ≤ lu.2 k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
