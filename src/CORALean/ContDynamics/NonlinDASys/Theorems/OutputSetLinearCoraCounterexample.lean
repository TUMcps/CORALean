module

public import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinearCora

@[expose] public section

/-!
# CORA's `nonlinDASys` output set ignores the algebraic variables

For the linear output `h(x, y, u) = y`, `NonlinDASys.outputSetLinearCora` is the single point
`h(p) = p_y`, whatever `R` is: the Jacobian in `x` is `0`, and the deviation of `y` from the center
`p_y` of its set `R_y` is in no term. A point `(x, y, u)` with `y ≠ p_y` has the output `y`, which
is not in the set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The output `y` of `h = y` at `y ≠ p_y` is not in CORA's output set, for any `R`, whatever
the dynamic and the constraint equation. -/
theorem NonlinDASys.outputSetLinearCora_counterexample
    (f : Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1) (g : Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1 → Vec ℝ 1)
    (R : S 1) (p_x p_u : Vec ℝ 1) (p_y x y u : Vec ℝ 1) (hy : y ≠ p_y) :
    let sys : NonlinDASys 1 1 1 := ⟨f, g, 1, fun _ y _ => y⟩
    sys.h x y u ∉ sys.outputSetLinearCora p_x p_y p_u R := by -- --- PROOF ---
  intro sys
  -- the Jacobian of `x ↦ p_y` is `0`, so every point of the set is `p_y`
  rintro ⟨x', -, hx'⟩
  have hJ : jacobianMat (fun _ : Vec ℝ 1 => p_y) p_x = 0 := by
    simp [jacobianMat]
  change y = p_y + jacobianMat (fun _ : Vec ℝ 1 => p_y) p_x *ᵥ (x' - p_x) at hx'
  rw [hJ, Matrix.zero_mulVec, add_zero] at hx'
  exact hy hx'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
