module

public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Operations.HitHessianMatZono
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapMatZono
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

@[expose] public section

/-!
# The enclosure `R_g` of the guard intersection

[1, Sec. 5.4]: `R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (−ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0))`, one `let`
per printed piece: `L` from [1, Prop. 2], `R_quad` by [1, Thm. 1] (`Zonotope.quadMapMatZono`) from
the matrix zonotopes of [1, Prop. 3] (`GuardMap.hitHessianMatZono`), `[φ̲, φ̄] ⊗ R_quad` by (10) and
(11), and `R_{h,E}(R(0))` with `I` of (16). A set, not a zonotope: `R_{h,E}(R(0))` is a product of
sets the paper does not reduce.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `E` – flow error set
* `R₀` – initial zonotope
* `ξ` – expansion point
* `ψc` – center of the coefficient enclosure
* `ψg` – generator of the coefficient enclosure
* `φlo` – lower end of the remainder factor
* `φhi` – upper end of the remainder factor

## Output
* set enclosing the guard intersection

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.4]: `R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (−ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0))`. -/
noncomputable def GuardMap.hitEnclosure (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (E : Set (Vec ℝ n)) (R₀ : Real.Zonotope (Vec ℝ n)) (ξ ψc ψg : Vec ℝ n) (φlo φhi : ℝ) :
    Set (Vec ℝ n) :=
  let yξ : Vec ℝ n := GuardMap.hitPoint A b nv d ξ                  -- `y_h(ξ)`
  let L : Mat ℝ n n := GuardMap.hitJacobian A b nv d ξ              -- `L = L(ξ)`
  let Rν : Real.Zonotope (Vec ℝ n) := ⟨R₀.h, R₀.c - ξ, R₀.G⟩        -- `R(0) ⊕ (−ξ)`
  let Q := GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg             -- `Q⁽ⁱ⁾`, Prop. 3
  let Rquad : Real.Zonotope (Vec ℝ n) :=                            -- `R_quad`, Thm. 1
    Real.Zonotope.quadMapMatZono (fun i => (Q i).c)
      (fun (j : Fin (1 + R₀.h + R₀.h)) i => (Q i).G j) Rν
  let Rφ : Set (Vec ℝ n) :=                                         -- `[φ̲, φ̄] ⊗ R_quad`
    ((φlo + φhi) / 2) • Rquad.construct + ((φhi - φlo) / 2) • Rquad.unitIntervalMul.construct
  let I : Set ℝ := (fun x => nv ⬝ᵥ (A *ᵥ x + b)) '' R₀.construct    -- `I`, (16)
  let RhE : Set (Vec ℝ n) :=                                        -- `R_{h,E}(R(0))`
    {z | ∃ x ∈ R₀.construct, ∃ e ∈ E, ∃ a ∈ I, z = (-(nv ⬝ᵥ e) / a) • (A *ᵥ x + b)} + E
  {yξ} + (fun ν => L *ᵥ ν) '' Rν.construct + (1 / 2 : ℝ) • Rφ + RhE

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
