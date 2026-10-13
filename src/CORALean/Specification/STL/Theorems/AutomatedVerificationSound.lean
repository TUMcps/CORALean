import CORALean.Specification.STL.Operations.AutomatedVerification

/-!
# [1, Alg. 3] is sound

Let `viol α` say that the trajectory of the factors `α ∈ box` violates `φ`. If `L = []` means
no `α` violates it (Alg. 2 on `φ`, `STL.factorCheck_sound`), a factor outside every polytope of
Alg. 2 on `¬φ` violates it (the same for `¬φ`), and `falsifiable L = true` means some `α ∈ box`
is in none of the polytopes `L` (the program (26), as corrected; see `STL.milpCorrected_iff`),
then `some true` means no factor violates `φ` and `some false` that one does. That is the
verdict of [1, Alg. 3] on all initial states and the piecewise constant inputs, which are inputs
of `U`. Termination, [1, Thm. 1], needs the reachable sets to converge and is not claimed.

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

variable {X 𝕋 : Type} [Div 𝕋] [OfNat 𝕋 2]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.automatedVerification_sound (tuneκ : 𝕋 → ℕ) (check checkNeg : 𝕋 → ℕ → List (Set X))
    (falsifiable : List (Set X) → Bool) (box : Set X) (viol : X → Prop)
    (hcheck : ∀ Δt κ, check Δt κ = [] → ∀ α ∈ box, ¬ viol α)
    (hneg : ∀ Δt κ α, α ∈ box → (∀ v ∈ checkNeg Δt κ, α ∉ v) → viol α)
    (hfals : ∀ L, falsifiable L = true → ∃ α ∈ box, ∀ v ∈ L, α ∉ v) (fuel : ℕ) (Δt : 𝕋) :
    (STL.automatedVerification tuneκ check checkNeg falsifiable fuel Δt = some true →
      ∀ α ∈ box, ¬ viol α) ∧
    (STL.automatedVerification tuneκ check checkNeg falsifiable fuel Δt = some false →
      ∃ α ∈ box, viol α) := by -- --- PROOF ---
  -- induction on the fuel, each halving of `Δt` one step
  induction fuel generalizing Δt with
  | zero => simp [STL.automatedVerification]
  | succ n ih =>
    unfold STL.automatedVerification
    dsimp only
    by_cases hL : (check Δt (tuneκ Δt)).isEmpty = true
    · -- safe
      rw [if_pos hL]
      exact ⟨fun _ => hcheck _ _ (List.isEmpty_iff.mp hL), fun h => (by cases h)⟩
    · rw [if_neg hL]
      by_cases hf : falsifiable (checkNeg Δt (tuneκ Δt)) = true
      · -- unsafe
        rw [if_pos hf]
        obtain ⟨α, hα, hnot⟩ := hfals _ hf
        exact ⟨fun h => (by cases h), fun _ => ⟨α, hα, hneg _ _ α hα hnot⟩⟩
      · rw [if_neg hf]
        exact ih (Δt / 2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
