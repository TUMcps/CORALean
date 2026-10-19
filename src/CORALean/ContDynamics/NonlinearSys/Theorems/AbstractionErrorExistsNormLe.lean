module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# A certified field is bounded along a confined continuous state

Where an abstraction error `L` is certified on `R × U`, the field is its affine part plus a
point of `L`. Along a state continuous on a compact time set and confined to `R`, under a fixed
input of `U`, the affine part is continuous, so bounded, and a bounded `L` bounds the rest: the
field is bounded along the state. It is what a classical solution needs to be integrable.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The field is bounded along a state continuous on a compact `K` and confined to `R`. -/
theorem AbstractionError.exists_norm_le {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {U : Set (Vec ℝ m)}
    {L : S n} (cert : AbstractionError f A B xs us R U L) (hL : Bornology.IsBounded (construct L))
    {x : ℝ → Vec ℝ n} {K : Set ℝ} (hK : IsCompact K) (hx : ContinuousOn x K)
    (hR : ∀ t ∈ K, x t ∈ R) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ U) : -- --- CONCL ---
    ∃ C, ∀ t ∈ K, ‖f (x t) u₀‖ ≤ C := by -- --- PROOF ---
  set a : ℝ → Vec ℝ n := fun t => f xs us + A *ᵥ (x t - xs) + B *ᵥ (u₀ - us)
  have ha : ContinuousOn a K :=
    (continuousOn_const.add ((Continuous.matrix_mulVec continuous_const
      continuous_id).comp_continuousOn (hx.sub continuousOn_const))).add continuousOn_const
  obtain ⟨Ca, hCa⟩ := hK.exists_bound_of_continuousOn ha
  obtain ⟨CL, hCL⟩ := hL.exists_norm_le
  refine ⟨CL + Ca, fun t ht => ?_⟩
  have h := hCL _ (cert.encloses (x t) (hR t ht) u₀ hu₀)
  calc ‖f (x t) u₀‖ = ‖(f (x t) u₀ - a t) + a t‖ := by rw [sub_add_cancel]
    _ ≤ ‖f (x t) u₀ - a t‖ + ‖a t‖ := norm_add_le _ _
    _ ≤ CL + Ca := add_le_add h (hCa t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
