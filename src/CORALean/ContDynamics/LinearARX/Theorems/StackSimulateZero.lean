module

public import CORALean.ContDynamics.LinearARX.Operations.Simulate

@[expose] public section

/-!
# The first window of a simulated run is the start window

`stack` at `0` reads the first `p` outputs, which `simulate` defines as the start
window's blocks. Shared by `simulate_trajectory` (real sets) and
`simulate_mem_simulateBox` (float boxes).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.stack_simulate_zero (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (u : ℕ → Vec ℝ du) : LinearARX.stack p (sys.simulate y₀ u) 0 = y₀ := by -- --- PROOF ---
  funext r
  have hlt : (0 + (finProdFinEquiv.symm r).1 : ℕ) < p := by
    simpa using (finProdFinEquiv.symm r).1.isLt
  have hs : sys.simulate y₀ u (0 + (finProdFinEquiv.symm r).1 : ℕ)
      = fun b => y₀ (finProdFinEquiv (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, b)) := by
    rw [LinearARX.simulate, dif_pos hlt]
  show sys.simulate y₀ u (0 + (finProdFinEquiv.symm r).1 : ℕ) (finProdFinEquiv.symm r).2 = _
  rw [hs]
  have hf : (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, (finProdFinEquiv.symm r).2)
      = finProdFinEquiv.symm r := Prod.ext (Fin.ext (zero_add _)) rfl
  show y₀ (finProdFinEquiv (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, _)) = _
  rw [hf, Equiv.apply_symm_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
