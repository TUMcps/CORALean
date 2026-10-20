module

public import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirard
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

@[expose] public section

/-!
# The dual bound of `Location.zonoGirardUpper` holds

A state `x` of the zonotope with `x·n = γ` has `x·ℓ = x·(ℓ - μ n) + μγ`, and `x·(ℓ - μ n)` is
at most the zonotope's support function in that direction, for every multiplier `μ`. The least
of finitely many such bounds is a bound.

## Inputs
* `Z` – zonotope
* `nv` – guard normal
* `γ` – guard offset
* `ℓ` – direction
* `x` – state

## Hypotheses
* `hx` – state lies in the zonotope
* `hg` – state lies on the guard

## Conclusion
* the state's direction value is at most the dual bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state of the zonotope on the hyperplane is below `zonoGirardUpper` along `ℓ`. -/
theorem Location.zonoGirardUpper_le (Z : Real.Zonotope (Vec ℝ n)) (nv : Vec ℝ n) (γ : ℝ)
    (ℓ : Vec ℝ n) {x : Vec ℝ n} (hx : x ∈ Z.construct) (hg : x ⬝ᵥ nv = γ) :
    x ⬝ᵥ ℓ ≤ Location.zonoGirardUpper Z nv γ ℓ := by -- --- PROOF ---
  -- the dual bound at a multiplier `μ`
  have hdual : ∀ μ : ℝ, x ⬝ᵥ ℓ ≤
      (ℓ - μ • nv) ⬝ᵥ Z.c + ∑ j, |(ℓ - μ • nv) ⬝ᵥ Z.G j| + μ * γ := fun μ => by
    let c : Vec ℝ n →ₗ[ℝ] ℝ :=
      { toFun := fun v => (ℓ - μ • nv) ⬝ᵥ v
        map_add' := fun a b => dotProduct_add _ _ _
        map_smul' := fun r a => by simp [dotProduct_smul] }
    have h := (Real.Zonotope.supportBound Z c).le x hx
    have h' : (ℓ - μ • nv) ⬝ᵥ x ≤ (ℓ - μ • nv) ⬝ᵥ Z.c + ∑ j, |(ℓ - μ • nv) ⬝ᵥ Z.G j| := h
    have e : x ⬝ᵥ ℓ = (ℓ - μ • nv) ⬝ᵥ x + μ * γ := by
      rw [sub_dotProduct, smul_dotProduct, dotProduct_comm nv x, hg, dotProduct_comm]
      simp
    linarith
  unfold Location.zonoGirardUpper
  set dual : ℝ → ℝ := fun μ => (ℓ - μ • nv) ⬝ᵥ Z.c + ∑ j, |(ℓ - μ • nv) ⬝ᵥ Z.G j| + μ * γ
    with hd
  have hdual' : ∀ μ : ℝ, x ⬝ᵥ ℓ ≤ dual μ := hdual
  -- the fold of `min` stays above `x·ℓ`
  have hfold : ∀ (l : List ℝ) (a : ℝ), x ⬝ᵥ ℓ ≤ a →
      x ⬝ᵥ ℓ ≤ l.foldl (fun m μ => min m (dual μ)) a := by
    intro l
    induction l with
    | nil => exact fun a h => h
    | cons μ l ih => exact fun a h => ih _ (le_min h (hdual' μ))
  exact hfold _ _ (hdual' 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
