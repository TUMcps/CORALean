module

public import CORALean.ContDynamics.NonlinDASys.Definitions.IsIndex1
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

@[expose] public section

/-!
# An index-1 system has a local reduced model

The algebraic variable as a function of state and input, near a consistent point: Mathlib's
implicit function theorem for a curried bivariate function (`implicitFunctionOfBivariate`) at
`G (x, u) y = g x y u`, whose partial in `y` is invertible by `IsIndex1At`. What it gives is local:
`ψ` solves the constraint near `(x₀, u₀)`, and `ψ (x, u) = y` is equivalent to the constraint
near `((x₀, u₀), y₀)`, so `ψ` is the unique solution there. A `ReducedModel` asks that
for all `x`, `u`, `y`; this is why one is data. `G₁`, `G₂` are the partial derivatives, continuous
at the point, which the theorem asks of `g` (`C¹` supplies them).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter
open scoped Topology

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.exists_localReduction (sys : NonlinDASys n p m)
    {x₀ : Vec ℝ n} {y₀ : Vec ℝ p} {u₀ : Vec ℝ m} (h₀ : sys.g x₀ y₀ u₀ = 0)
    (hI : sys.IsIndex1At x₀ y₀ u₀)
    {G₁ : Vec ℝ n × Vec ℝ m → Vec ℝ p → (Vec ℝ n × Vec ℝ m) →L[ℝ] Vec ℝ p}
    {G₂ : Vec ℝ n × Vec ℝ m → Vec ℝ p → Vec ℝ p →L[ℝ] Vec ℝ p}
    (d₁ : ∀ᶠ v in 𝓝 ((x₀, u₀), y₀),
      HasFDerivAt (fun xu : Vec ℝ n × Vec ℝ m => sys.g xu.1 v.2 xu.2) (G₁ v.1 v.2) v.1)
    (d₂ : ∀ᶠ v in 𝓝 ((x₀, u₀), y₀),
      HasFDerivAt (fun y' => sys.g v.1.1 y' v.1.2) (G₂ v.1 v.2) v.2)
    (c₁ : ContinuousAt (Function.HasUncurry.uncurry G₁) ((x₀, u₀), y₀))
    (c₂ : ContinuousAt (Function.HasUncurry.uncurry G₂) ((x₀, u₀), y₀)) :
    ∃ ψ : Vec ℝ n × Vec ℝ m → Vec ℝ p, ψ (x₀, u₀) = y₀ ∧
      (∀ᶠ xu in 𝓝 (x₀, u₀), sys.g xu.1 (ψ xu) xu.2 = 0) ∧
      ∀ᶠ v in 𝓝 ((x₀, u₀), y₀), sys.g v.1.1 v.2 v.1.2 = 0 ↔ ψ v.1 = v.2 := by -- --- PROOF ---
  obtain ⟨L, hL, hLinv⟩ := hI
  have hG₂ : G₂ (x₀, u₀) y₀ = L := (d₂.self_of_nhds.unique hL)
  have inv : (G₂ (x₀, u₀) y₀).IsInvertible := hG₂ ▸ hLinv
  set G : Vec ℝ n × Vec ℝ m → Vec ℝ p → Vec ℝ p := fun xu y => sys.g xu.1 y xu.2
  refine ⟨implicitFunctionOfBivariate (f := G) d₁ d₂ c₁ c₂ inv, ?_, ?_, ?_⟩
  · have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate (f := G) d₁ d₂ c₁ c₂ inv)
    have := h.self_of_nhds
    exact this.mp rfl
  · have h := eventually_apply_implicitFunctionOfBivariate (f := G) d₁ d₂ c₁ c₂ inv
    filter_upwards [h] with xu hxu
    simpa [G, h₀] using hxu
  · have h := eventually_apply_eq_iff_implicitFunctionOfBivariate (f := G) d₁ d₂ c₁ c₂ inv
    filter_upwards [h] with v hv
    simpa [G, h₀] using hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
