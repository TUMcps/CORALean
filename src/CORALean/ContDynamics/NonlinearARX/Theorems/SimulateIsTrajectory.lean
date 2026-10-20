module

public import CORALean.ContDynamics.NonlinearARX.Operations.Simulate

@[expose] public section

/-!
# A simulated run is a trajectory

From a start window in `Y₀` and inputs in `U`, the sampled outputs are exactly what
`IsTrajectory` asks of a run: the recursion holds from `p` on by definition, and the first
window is `y₀` read back through the same block indexing.

## Inputs
* `sys` – ARX system
* `Y₀` – initial window set
* `U` – input set
* `y₀` – start window
* `u` – inputs

## Hypotheses
* `hy₀` – start window lies in `Y₀`
* `hu` – inputs lie in `U`

## Conclusion
* the simulated run is a trajectory
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.simulate_isTrajectory (sys : NonlinearARX dy du p) {Y₀ : S (p * dy)}
    {U : S du} {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U) : sys.IsTrajectory Y₀ U (sys.simulate y₀ u) u where
  init := by
    -- the window of the first `p` outputs is `y₀` itself
    have h : NonlinearARX.stack p (sys.simulate y₀ u) 0 = y₀ := by
      funext r
      have hlt : (0 + (finProdFinEquiv.symm r).1 : ℕ) < p := by
        simpa using (finProdFinEquiv.symm r).1.isLt
      have hs : sys.simulate y₀ u (0 + (finProdFinEquiv.symm r).1 : ℕ)
          = fun b => y₀ (finProdFinEquiv (⟨0 + (finProdFinEquiv.symm r).1, hlt⟩, b)) := by
        rw [NonlinearARX.simulate, dif_pos hlt]
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
    rw [NonlinearARX.simulate, dif_neg (not_lt.mpr hk)]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
