module

public import CORALean.Global.EqAddIntegralOfHasDerivWithinAt
public import CORALean.HybridDynamics.Definitions.Location
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# A classical stay is a stay

A state with the derivative `A x + B u + c + E w` within `[0, τ]` at every point, under a
continuous input and disturbance, is a stay: the integrand is then continuous, so measurable and
integrable, and the fundamental theorem of calculus gives the integral equation `IsTrajectory`
states. It is how a stay written down in closed form is shown to be one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay with the whole equation's right-hand side as its derivative, under a continuous input
and disturbance, is a stay. -/
theorem Location.IsTrajectory.of_hasDerivWithinAt {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ ℓ.dynamics.m} {w : ℝ → Vec ℝ ℓ.dynamics.r} (nonneg : 0 ≤ τ)
    (input : ∀ t ∈ Set.Icc 0 τ, u t ∈ construct ℓ.U)
    (dist : ∀ t ∈ Set.Icc 0 τ, w t ∈ construct ℓ.W)
    (hu : ContinuousOn u (Set.Icc 0 τ)) (hw : ContinuousOn w (Set.Icc 0 τ))
    (hd : ∀ t ∈ Set.Icc 0 τ, HasDerivWithinAt x (toRealMat ℓ.dynamics.A *ᵥ x t +
      toRealMat ℓ.dynamics.B *ᵥ u t + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w t)
        (Set.Icc 0 τ) t)
    (invariant : ∀ t ∈ Set.Icc 0 τ, x t ∈ construct ℓ.inv) : -- --- CONCL ---
    ℓ.IsTrajectory τ x u w := by -- --- PROOF ---
  have hx : ContinuousOn x (Set.Icc 0 τ) := fun t ht => (hd t ht).continuousWithinAt
  -- the right-hand side along the stay is continuous, so measurable and integrable
  have hf : ContinuousOn (fun s => toRealMat ℓ.dynamics.A *ᵥ x s +
      toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s)
      (Set.Icc 0 τ) :=
    ((((continuous_const.matrix_mulVec continuous_id).comp_continuousOn hx).add
      ((continuous_const.matrix_mulVec continuous_id).comp_continuousOn hu)).add
        continuousOn_const).add
      ((continuous_const.matrix_mulVec continuous_id).comp_continuousOn hw)
  have hint : ∀ t ∈ Set.Icc 0 τ, IntervalIntegrable (fun s => toRealMat ℓ.dynamics.A *ᵥ x s +
      toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s)
      volume 0 t := fun t ht =>
    (hf.mono (Set.uIcc_subset_Icc ⟨le_rfl, nonneg⟩ ht)).intervalIntegrable
  exact ⟨nonneg, input, dist, hf.aestronglyMeasurable measurableSet_Icc, hint, hx,
    fun t ht => eq_add_integral_of_hasDerivWithinAt (convex_Icc 0 τ) ⟨le_rfl, nonneg⟩ hd ht
      (hint t ht), invariant⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
