module

public import CORALean.NN.Layers.Definitions.ApproxErrorRelaxation
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorEnclosure

@[expose] public section

/-!
# The image enclosure of a nonlinear layer is sound

[1, Alg. 1]: for a continuous activation `ϕ`, `m x ⊕ [e_low, e_up]` encloses `ϕ([l, u])` at every
box, so the relaxation `approxErrorRelaxation ϕ` is sound for `ϕ`, and so is the layer built on it
(`Layer.activation_sound`). The proof is [1, Def. 6]'s enclosure: `e_low ≤ ϕ(t) - m t ≤ e_up`,
recentered.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxErrorRelaxation_sound {ϕ : ℝ → ℝ} (hϕ : Continuous ϕ) :
    (approxErrorRelaxation ϕ).Sound ϕ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  change l ≤ t at hl
  change t ≤ u at hu
  have hc : ContinuousOn (fun x => ϕ x - (fun x => secantSlope ϕ l u * x) x) (Set.Icc l u) :=
    (hϕ.sub (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨h1, h2⟩ := approxError_enclosure ϕ (fun x => secantSlope ϕ l u * x) l u hc t ⟨hl, hu⟩
  show |ϕ t - ((approxErrorRelaxation ϕ).slope l u * t + (approxErrorRelaxation ϕ).offset l u)|
    ≤ (approxErrorRelaxation ϕ).error l u
  simp only [approxErrorRelaxation]
  rw [abs_le]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
