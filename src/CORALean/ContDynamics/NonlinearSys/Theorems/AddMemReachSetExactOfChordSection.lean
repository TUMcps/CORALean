module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAt
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffSubsetOfContinuousOfConvex
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# The eroded chord union is reached where its chords are chosen continuously

[1, Prop. 2] with `⊖` taken over the whole chord union `⋃_{t∈[0,Δt]} {x₀ + (t/Δt)(Mx₀ + v - x₀)}`:
a point `z + 2c` of `(⋃ chords ⊖ E) + 2c`, `E = C ⊕ R̂_err` centrally symmetric about `c`, lies in
`R(τ₀)` when the chords cover `z + E` through a continuous choice `σ` of start `x₀ ∈ X₀` and time
`t`. Brouwer's theorem on `z + E` then finds a point whose chosen solution lands on `z + 2c`;
Grönwall makes `(x₀, t) ↦ x(t)` continuous. Without such a choice the claim is false, for a
convex `X₀` too (`NonlinearSys.minkowskiDiff_iUnion_chord_convex_counterexample`). That
every solution stays within `E` of its chord is a hypothesis, as in
`NonlinearSys.minkowskiDiff_chord_subset_reachSetExact`, the case of a constant time.

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
* `z` – point of the eroded chord union, before the shift
* `σ` – chosen start and time

## Hypotheses
* `hE` – error set compact
* `hEc` – error set convex
* `hEne` – error set nonempty
* `hEs` – error set symmetric about center
* `hu₀` – input in input set
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start
* `herr` – solutions lie within the error set of their chord
* `hσc` – choice continuous on the shifted error set
* `hσ` – choice is a start in the initial set and a time whose chord hits the point

## Conclusion
* the shifted point lies in the exact time-interval reachable set

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] over the whole chord union: `z + 2c ∈ R(τ₀)` when the chords cover `z + E`
through a start and time `σ` chosen continuously. -/
theorem NonlinearSys.add_mem_reachSetExact_of_chord_section (sys : NonlinearSys n m)
    (R₀ : S n) (U : S m) {Δt : ℝ} (M : Mat ℝ n n) (v : Vec ℝ n)
    {E : Set (Vec ℝ n)} (hE : IsCompact E) (hEc : Convex ℝ E) (hEne : E.Nonempty) {c : Vec ℝ n}
    (hEs : ∀ e ∈ E, (2 : ℝ) • c - e ∈ E) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ construct U)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ construct R₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t)
    (herr : ∀ t ∈ Set.Icc 0 Δt, ∀ x₀ ∈ construct R₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ s ∈ Set.Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Set.Icc 0 t) s) →
      x t - (x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) ∈ E)
    {z : Vec ℝ n} (σ : Vec ℝ n → Vec ℝ n × ℝ) (hσc : ContinuousOn σ ((z + ·) '' E))
    (hσ : ∀ p ∈ (z + ·) '' E, (σ p).1 ∈ construct R₀ ∧ (σ p).2 ∈ Set.Icc 0 Δt ∧
      (σ p).1 + ((σ p).2 / Δt) • (M *ᵥ (σ p).1 + v - (σ p).1) = p) : -- --- CONCL ---
    z + (2 : ℝ) • c ∈
      ⋃ t ∈ Set.Icc 0 Δt, sys.reachSetExact (Set.Icc 0 t) R₀ U t := by -- --- PROOF ---
  classical
  set X₀ := construct R₀
  choose sol hsol0 hsol using hex
  set F : Vec ℝ n × ℝ → Vec ℝ n := fun q => if h : q.1 ∈ X₀ then sol q.1 h q.2 else 0
  -- each solution is continuous on `[0, Δt]` and solves the equation from the right
  have hcont : ∀ x₀ (h : x₀ ∈ X₀), ContinuousOn (sol x₀ h) (Set.Icc 0 Δt) := fun x₀ h t ht =>
    (hsol x₀ h t ht).2.continuousWithinAt
  have hIci : ∀ x₀ (h : x₀ ∈ X₀), ∀ t ∈ Set.Ico 0 Δt,
      HasDerivWithinAt (sol x₀ h) (sys.f (sol x₀ h t) u₀) (Set.Ici t) t := fun x₀ h t ht =>
    (hsol x₀ h t (Set.Ico_subset_Icc_self ht)).2.mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Set.Icc_subset_Icc_left ht.1))
  -- Grönwall: `x₀ ↦ x(t)` is `e^{KΔt}`-Lipschitz on `X₀` at every `t`, so `F` is continuous
  have hF : ContinuousOn F (X₀ ×ˢ Set.Icc 0 Δt) := by
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith F
      ⟨Real.exp (K * Δt), (Real.exp_pos _).le⟩ (fun a ha => ?_) (fun t ht => ?_)
    · refine (hcont a ha).congr fun s _ => ?_
      simp only [F, dif_pos ha]
    · refine LipschitzOnWith.of_dist_le_mul fun b hb b' hb' => ?_
      have hd := dist_le_of_trajectories_ODE_of_mem (v := fun _ x => sys.f x u₀)
        (s := fun _ => Ω) (fun _ _ => hLip) (hcont b hb) (hIci b hb)
        (fun t ht => (hsol b hb t (Set.Ico_subset_Icc_self ht)).1) (hcont b' hb') (hIci b' hb')
        (fun t ht => (hsol b' hb' t (Set.Ico_subset_Icc_self ht)).1)
        (le_of_eq (by rw [hsol0 b hb, hsol0 b' hb'])) t ht
      have hk : Real.exp (K * t) ≤ Real.exp (K * Δt) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.2)
      simp only [F, dif_pos hb, dif_pos hb']
      calc _ ≤ dist b b' * Real.exp (K * (t - 0)) := hd
        _ ≤ dist b b' * Real.exp (K * Δt) := by
          rw [sub_zero]; exact mul_le_mul_of_nonneg_left hk dist_nonneg
        _ = _ := by rw [mul_comm]; rfl
  -- the error `φ(p) = x(t) - p` of the chosen start and time, on `z + E`
  set φ : Vec ℝ n → Vec ℝ n := fun p => F (σ p) - p
  have hσX : Set.MapsTo σ ((z + ·) '' E) (X₀ ×ˢ Set.Icc 0 Δt) := fun p hp =>
    ⟨(hσ p hp).1, (hσ p hp).2.1⟩
  have hφ : ContinuousOn φ ((z + ·) '' E) := (hF.comp hσc hσX).sub continuousOn_id
  have hφE : Set.MapsTo φ ((z + ·) '' E) E := fun p hp => by
    obtain ⟨h0, ht, hp'⟩ := hσ p hp
    show F (σ p) - p ∈ E
    have h := herr _ ht _ h0 _ (hsol0 _ h0) fun s hs =>
      (hsol _ h0 s ⟨hs.1, hs.2.trans ht.2⟩).2.mono (Set.Icc_subset_Icc_right ht.2)
    rw [hp'] at h
    simpa only [F, dif_pos h0] using h
  -- Brouwer on `z + E`: some `p + φ(p)`, a solution's value, is `z + 2c`
  have hz : z ∈ minkowskiDiff ((z + ·) '' E) E := fun e he => ⟨e, he, rfl⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hzp⟩ := minkowskiDiff_subset_of_continuous_of_convex hE hEc hEne hEs
    hφ hφE hz
  obtain ⟨h0, ht, -⟩ := hσ p hp
  have hval : z + (2 : ℝ) • c = sol (σ p).1 h0 (σ p).2 := by
    rw [← hzp]
    simp only [φ]
    rw [show F (σ p) = sol (σ p).1 h0 (σ p).2 from dif_pos h0]
    abel
  -- the solution, restricted to `[0, t]`, is a run
  have hfc : ContinuousOn (fun s => sys.f (sol (σ p).1 h0 s) u₀) (Set.Icc 0 (σ p).2) :=
    hLip.continuousOn.comp ((hcont (σ p).1 h0).mono (Set.Icc_subset_Icc_right ht.2))
      fun s hs => (hsol (σ p).1 h0 s ⟨hs.1, hs.2.trans ht.2⟩).1
  refine Set.mem_iUnion₂.mpr ⟨(σ p).2, ht, sol (σ p).1 h0, fun _ => u₀,
    NonlinearSys.IsTrajectory.of_hasDerivWithinAt (convex_Icc 0 (σ p).2) ⟨le_rfl, ht.1⟩
      (by rw [hsol0 (σ p).1 h0]; exact h0) (fun _ _ => hu₀)
      (fun s hs => (hsol (σ p).1 h0 s ⟨hs.1, hs.2.trans ht.2⟩).2.mono
        (Set.Icc_subset_Icc_right ht.2))
      (fun s hs => (hfc.mono (Set.uIcc_subset_Icc ⟨le_rfl, ht.1⟩ hs)).intervalIntegrable),
    hval.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
