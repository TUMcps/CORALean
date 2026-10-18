module

public import CORALean.ContDynamics.NonlinDASys.Operations.ConsistentInitialState
public import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonIterateSpec

@[expose] public section

/-!
# What `consistentInitialState` returns

The returned `y'` is `y + Δy` for an iterate `y`, where `Δy` has norm below `tol`, the code's own
stopping test, and, when `F` is invertible there, solves `F Δy = -g(x₀, y, u₀)`: a Newton step.
The test is on the step, not the residual, so `g(x₀, y', u₀) = 0` is not claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result is a Newton step of norm below `tol` taken from some iterate. -/
theorem NonlinDASys.consistentInitialState_spec (sys : NonlinDASys n p m)
    (F : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p p) (tol : ℝ) (fuel : ℕ) (x₀ : Vec ℝ n)
    (u₀ : Vec ℝ m) (y₀ y' : Vec ℝ p)
    (h : sys.consistentInitialState F tol fuel x₀ u₀ y₀ = some y') : -- --- STMT ---
    ∃ y Δ : Vec ℝ p, y' = y + Δ ∧ norm₂ Δ < tol ∧
      (IsUnit (F x₀ y u₀).det → F x₀ y u₀ *ᵥ Δ = -(sys.g x₀ y u₀)) := by -- --- PROOF ---
  obtain ⟨y, hy, hs⟩ := newtonIterate_spec _ _ fuel y₀ y' h
  refine ⟨y, _, hy, of_decide_eq_true hs, fun hdet => ?_⟩
  -- `F (F⁻¹ v) = v` for an invertible `F`
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
