module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAt
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffSubsetOfContinuousOfConvex
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The Minkowski difference as an inner time-point reachable set

[1, Prop. 1]: for a compact initial set `X₀` and the centrally symmetric error set `R̂_err` of
[1, Eq. 13] (a zonotope, so convex and compact), `R̂(Δt) = R_aff(Δt) ⊖ R̂_err + 2c` lies in the
exact reachable set `R(Δt)` (20), `c = cen(R̂_err)`, `R_aff(Δt) = e^{AΔt} X₀ + R_con(Δt)`. The
representation (21) is restated from the conservative-linearization papers and is a hypothesis
(`herr`), as are the solutions (`hex`) and the Lipschitz constant of the field (`hLip`);
`IsTrajectory.sub_mem_inputSolution` derives (21). What [1] adds is proved: Grönwall makes
`x₀ ↦ x(Δt)` continuous, and `minkowskiDiff_subset_of_continuous_of_convex` gives the inclusion.
The printed proof applies [1, Lemma 1] with a set not convex for a nonconvex `X₀`.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `Δt` – step size
* `M` – transition matrix
* `v` – particular solution
* `E` – error set
* `c` – center of symmetry
* `u₀` – constant input
* `Ω` – Lipschitz region
* `K` – Lipschitz constant

## Hypotheses
* `hΔt` – step size nonnegative
* `hM` – matrix invertible
* `hE` – error set compact
* `hEc` – error set convex
* `hEne` – error set nonempty
* `hEs` – error set symmetric about center
* `hu₀` – input in input set
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start
* `herr` – solutions have the error representation

## Conclusion
* the shifted Minkowski difference lies in the exact reachable set

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `R_aff(Δt) ⊖ R̂_err + 2c ⊆ R(Δt)`, given the representation (21) of every
solution under the input `u₀` and the field `K`-Lipschitz along them. -/
theorem NonlinearSys.minkowskiDiff_add_subset_reachSetExact (sys : NonlinearSys n m) (R₀ : S n)
    (U : S m) {Δt : ℝ} (hΔt : 0 ≤ Δt) (M : Mat ℝ n n) (hM : IsUnit M.det) (v : Vec ℝ n)
    {E : Set (Vec ℝ n)} (hE : IsCompact E) (hEc : Convex ℝ E) (hEne : E.Nonempty)
    {c : Vec ℝ n} (hEs : ∀ e ∈ E, (2 : ℝ) • c - e ∈ E) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ construct U)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ construct R₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t)
    (herr : ∀ x₀ ∈ construct R₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t) →
      x Δt - (M *ᵥ x₀ + v) ∈ E) : -- --- CONCL ---
    (fun s => s + (2 : ℝ) • c) '' minkowskiDiff ((fun x₀ => M *ᵥ x₀ + v) '' construct R₀) E
      ⊆ sys.reachSetExact (Set.Icc 0 Δt) R₀ U Δt := by -- --- PROOF ---
  classical
  set X₀ := construct R₀
  choose sol hsol0 hsol using hex
  set ξ : Vec ℝ n → Vec ℝ n := fun x₀ => if h : x₀ ∈ X₀ then sol x₀ h Δt else 0
  -- each solution is continuous on `[0, Δt]` and solves the equation from the right
  have hcont : ∀ x₀ (h : x₀ ∈ X₀), ContinuousOn (sol x₀ h) (Set.Icc 0 Δt) := fun x₀ h t ht =>
    (hsol x₀ h t ht).2.continuousWithinAt
  have hIci : ∀ x₀ (h : x₀ ∈ X₀), ∀ t ∈ Set.Ico 0 Δt,
      HasDerivWithinAt (sol x₀ h) (sys.f (sol x₀ h t) u₀) (Set.Ici t) t := fun x₀ h t ht =>
    (hsol x₀ h t (Set.Ico_subset_Icc_self ht)).2.mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Set.Icc_subset_Icc_left ht.1))
  -- Grönwall: `x₀ ↦ x(Δt)` is Lipschitz on `X₀`
  have hξ : ContinuousOn ξ X₀ := by
    refine (LipschitzOnWith.of_dist_le_mul
      (K := ⟨Real.exp (K * Δt), (Real.exp_pos _).le⟩) fun a ha b hb => ?_).continuousOn
    simp only [ξ, dif_pos ha, dif_pos hb]
    have h := dist_le_of_trajectories_ODE_of_mem (v := fun _ x => sys.f x u₀) (s := fun _ => Ω)
      (fun _ _ => hLip) (hcont a ha) (hIci a ha)
      (fun t ht => (hsol a ha t (Set.Ico_subset_Icc_self ht)).1) (hcont b hb) (hIci b hb)
      (fun t ht => (hsol b hb t (Set.Ico_subset_Icc_self ht)).1)
      (le_of_eq (by rw [hsol0 a ha, hsol0 b hb])) Δt ⟨hΔt, le_rfl⟩
    rwa [sub_zero, mul_comm] at h
  -- the error `z(x₀) = x(Δt) - (M x₀ + v)` as a function of `a = M x₀ + v`
  have hinv : ∀ x₀, M⁻¹ *ᵥ (M *ᵥ x₀ + v - v) = x₀ := fun x₀ => by
    rw [add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM,
      Matrix.one_mulVec]
  set φ : Vec ℝ n → Vec ℝ n := fun a => ξ (M⁻¹ *ᵥ (a - v)) - a
  have hφx : ∀ x₀ (h : x₀ ∈ X₀), φ (M *ᵥ x₀ + v) = sol x₀ h Δt - (M *ᵥ x₀ + v) :=
    fun x₀ h => by simp only [φ]; rw [hinv, show ξ x₀ = sol x₀ h Δt from dif_pos h]
  have hmaps : Set.MapsTo (fun a => M⁻¹ *ᵥ (a - v)) ((fun x₀ => M *ᵥ x₀ + v) '' X₀) X₀ := by
    rintro _ ⟨x₀, hx₀, rfl⟩; simpa only [hinv] using hx₀
  have hφ : ContinuousOn φ ((fun x₀ => M *ᵥ x₀ + v) '' X₀) :=
    (hξ.comp (continuous_const.matrix_mulVec (continuous_id.sub continuous_const)).continuousOn
      hmaps).sub continuousOn_id
  have hφE : Set.MapsTo φ ((fun x₀ => M *ᵥ x₀ + v) '' X₀) E := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [hφx x₀ hx₀]
    exact herr x₀ hx₀ (sol x₀ hx₀) (hsol0 x₀ hx₀) fun t ht => (hsol x₀ hx₀ t ht).2
  -- Lemma 1 in its convex-error form, and every point it gives is some `x(Δt)`
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨_, ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩, rfl⟩ :=
    minkowskiDiff_subset_of_continuous_of_convex hE hEc hEne hEs hφ hφE hy
  -- the solution is a run: the field along it is continuous, `f(·, u₀)` Lipschitz on `Ω`
  have hfc : ContinuousOn (fun t => sys.f (sol x₀ hx₀ t) u₀) (Set.Icc 0 Δt) :=
    hLip.continuousOn.comp (hcont x₀ hx₀) fun s hs => (hsol x₀ hx₀ s hs).1
  refine ⟨sol x₀ hx₀, fun _ => u₀, NonlinearSys.IsTrajectory.of_hasDerivWithinAt
    (convex_Icc 0 Δt) ⟨le_rfl, hΔt⟩ (by rw [hsol0 x₀ hx₀]; exact hx₀) (fun _ _ => hu₀)
    (fun t ht => (hsol x₀ hx₀ t ht).2)
    (fun t ht => (hfc.mono (Set.uIcc_subset_Icc ⟨le_rfl, hΔt⟩ ht)).intervalIntegrable), ?_⟩
  simp only
  rw [hφx x₀ hx₀]
  abel_nf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
