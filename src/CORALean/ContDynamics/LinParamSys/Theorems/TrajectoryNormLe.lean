import CORALean.ContDynamics.LinParamSys.LinParamSys

/-!
# How far a time-varying run can get, a priori

Grönwall's inequality at `‖ẋ‖ ≤ ‖A t‖ ‖x‖ + ‖u t‖`: a bound on the state over a
window that needs no solution and no matrix exponential, only bounds on the
matrix set and on the input set. It is what makes the drift `(A t - Â) x t` of
`Trajectory.toLinearSys` bounded, and so the enlarged input set constructible —
without it that theorem's `hV` is a hypothesis about the run itself.

`M` and `ν` are read off the two sets a `LinParamSys` carries, `δ` off the
initial set, so every constant here is available before a run is fixed.

The derivative is asked within `Ici t`, which `Trajectory.flow` does not give
directly: `T` need not extend left of `t`, but `Set.Icc a b ⊆ T` with
`t ∈ Ico a b` says it extends right, and that is what [1] needs.

## References

* [1] T. H. Gronwall. "Note on the derivatives with respect to a parameter of
      the solutions of a system of differential equations". Annals of
      Mathematics, 20(4):292-296, 1919.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `‖A t‖ ≤ M` and `‖u t‖ ≤ ν` over the window, the state never leaves the
Grönwall bound of its starting norm. -/
theorem LinParamSys.Trajectory.norm_le {sys : LinParamSys 𝕄 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {a b : ℝ} (hT : Set.Icc a b ⊆ T) {M ν δ : ℝ}
    (hM : ∀ t ∈ Set.Ico a b, ‖A t‖ ≤ M) (hν : ∀ t ∈ Set.Ico a b, ‖u t‖ ≤ ν)
    (hδ : ‖x a‖ ≤ δ) :
    ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ gronwallBound δ M ν (t - a) := by -- --- PROOF ---
  -- the flow gives continuity on the window, `T` being no smaller than it
  have hcont : ContinuousOn x (Set.Icc a b) := fun t ht =>
    ((traj.flow t (hT ht)).continuousWithinAt).mono hT
  -- and a right derivative wherever the window still extends to the right
  have hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt x (A t *ᵥ x t + u t) (Set.Ici t) t := fun t ht =>
    (traj.flow t (hT ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Ico_subset.mpr
        ⟨b, ht.2, fun _ hs => hT ⟨le_trans ht.1 hs.1, hs.2.le⟩⟩)
  refine norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv hδ fun t ht => ?_
  -- the vector field is bounded by `M ‖x‖ + ν`, which is Grönwall's hypothesis
  refine le_trans (norm_add_le _ _) (add_le_add ?_ (hν t ht))
  exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
    (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
