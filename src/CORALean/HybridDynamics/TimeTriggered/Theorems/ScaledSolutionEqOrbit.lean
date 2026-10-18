module

public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionUnscale

@[expose] public section

/-!
# The scaled solution is on the orbit, at the clock

[1, Sec. 3.2]: a solution `y` of `ẏ = g(y) f(y)` that starts where a solution `z` of `ẋ = f(x)`
starts is, while its clock `∫₀ᵗ g(y)` has not passed the horizon `M` of `z`, at `z` of the clock:
the reparametrization of `scaledSolution_unscale` and uniqueness of solutions of `ẋ = f(x)`.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.2]: `y(t) = z(∫₀ᵗ g(y))` while the clock stays within the horizon of `z`. -/
theorem scaledSolution_eq_orbit {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {g : X → ℝ}
    (hg : Continuous g) {y z : ℝ → X} {t M : ℝ} (ht : 0 ≤ t)
    (hy0 : ∀ u ∈ Icc 0 t, 0 ≤ g (y u)) (hyc : ContinuousOn y (Icc 0 t))
    (hyd : ∀ u ∈ Ico 0 t, HasDerivWithinAt y (g (y u) • f (y u)) (Ici u) u)
    (hz : ∀ u ∈ Icc 0 M, HasDerivAt z (f (z u)) u) (hz0 : z 0 = y 0)
    (hσ : ∫ v in (0 : ℝ)..t, g (y v) ≤ M) : -- --- STMT ---
    y t = z (∫ v in (0 : ℝ)..t, g (y v)) := by -- --- PROOF ---
  obtain ⟨γ, hγ0, hγ, hγt⟩ := scaledSolution_unscale hf hg ht hy0 hyc hyd
  have hσ0 : 0 ≤ ∫ v in (0 : ℝ)..t, g (y v) :=
    intervalIntegral.integral_nonneg ht fun u hu => hy0 u hu
  rw [← hγt]
  exact lipschitzSolution_unique hf hγ (fun u hu => hz u ⟨hu.1, hu.2.trans hσ⟩)
    (hγ0.trans hz0.symm) _ ⟨hσ0, le_rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
