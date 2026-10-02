import CORALean.ContDynamics.LinearARX.Operations.Simulate

/-!
# A simulated run is a trajectory

From a start window in `Y₀` and inputs in `U`, the sampled outputs are exactly what
`Trajectory` asks of a run: the recursion holds from `p` on by definition, and the first
window is `y₀` read back through the same block indexing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_trajectory (sys : LinearARX 𝕋 dy du p) {Y₀ : S (p * dy)} {U : S du}
    {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U) : sys.Trajectory Y₀ U (sys.simulate y₀ u) u where
  init := by
    -- the window of the first `p` outputs is `y₀` itself
    have h : LinearARX.stack p (sys.simulate y₀ u) 0 = y₀ := by
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
    rw [h]
    exact hy₀
  input := hu
  step k hk := by
    rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
