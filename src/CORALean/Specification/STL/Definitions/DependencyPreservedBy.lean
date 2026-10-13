module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# Dependency preservation

[1, Def. 4]: for the solution `ξ(t, x₀, u(·))` and a reachable set enclosure `R(t)` on `[0, t_end]`,
a function `μ(t, x₀, u(·))` and an error set `E(t)` with `ξ(t, x₀, u(·)) ∈ μ(t, x₀, u(·)) ⊕ E(t) ⊆
R(t)` for all `x₀ ∈ X₀` and `u(·) ∈ 𝒰`, the trivial solution `μ = 0`, `E = R` allowed only for a
singleton `R(t)`. "Can be used to construct" has no formal content in [1]: `μ` and `E` are
quantified, not computed from `R`. `STL.dependencyPreserving_of_encloses` shows what that gives.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X Y : Type} [AddCommGroup X]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 4] for `μ` and `E`: `ξ ∈ μ ⊕ E ⊆ R` on `[0, t_end]`, and `μ = 0`, `E = R` only if `R`
is a singleton. -/
def STL.DependencyPreservedBy (ξ : ℝ → X → (ℝ → Y) → X) (X₀ : Set X) (𝒰 : Set (ℝ → Y))
    (R : ℝ → Set X) (tEnd : ℝ) (μ : ℝ → X → (ℝ → Y) → X) (E : ℝ → Set X) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) tEnd, (∀ x₀ u, μ t x₀ u = 0) → E t = R t → ∃ r, R t = {r}) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) tEnd, ∀ x₀ ∈ X₀, ∀ u ∈ 𝒰,
    ξ t x₀ u ∈ (fun e => μ t x₀ u + e) '' E t ∧ (fun e => μ t x₀ u + e) '' E t ⊆ R t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
