module

public import CORALean.ContSet.Zonotope.Real.Definitions.FRadius

@[expose] public section

/-!
# The set-based loss

[1, Def. 5]: `𝓛(t, Y) = (1 - τ) L(t, c_κ) + (τ/ε) ‖Y‖_F` for an output zonotope `Y = ⟨c_κ, G_κ⟩`, a
loss `L` of target and output, the tradeoff `τ ∈ [0, 1]` and the perturbation radius `ε > 0`. The
first term is the standard loss of the centre (accuracy), the second the F-radius of the
enclosure (robustness), normalized by `ε`; `ε` and `τ` are not constrained here, what is proved
about them says which values it needs.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(1 - τ) L(t, c) + (τ/ε) ‖Y‖_F`. -/
noncomputable def setBasedLoss (L : Vec ℝ n → Vec ℝ n → ℝ) (τ ε : ℝ) (t : Vec ℝ n)
    (Y : Zonotope (Vec ℝ n)) : ℝ :=
  (1 - τ) * L t Y.c + τ / ε * Y.fRadius

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
