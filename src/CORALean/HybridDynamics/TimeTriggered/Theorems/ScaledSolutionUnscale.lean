module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution

@[expose] public section

/-!
# A solution of the scaled field is a solution of the field, reparametrized

[1, Sec. 3.2]: along `ẏ = g(y) f(y)` with `g(y) ≥ 0` the state moves along the orbit of `ẋ = f(x)`,
only at another speed. With `σ(u) = ∫₀ᵘ g(y)` and `γ` the solution of `ẋ = f(x)` from `y(0)`,
`y(u) = γ(σ(u))`: both solve `v̇ = g(y(u)) f(v)`, whose right-hand side is Lipschitz in `v` with the
constant `K · sup g(y)`, so they agree. This is what the printed proof of [1, Lemma 2] means by "the
point `x'` will eventually be the continuous part of a reachable state of `H`".

## Inputs
* `f` – vector field
* `K` – Lipschitz constant
* `g` – scaling function
* `y` – scaled solution
* `t` – duration

## Hypotheses
* `hf` – field is Lipschitz
* `hg` – scaling function continuous
* `ht` – duration nonnegative
* `hy0` – scaling function nonnegative along the curve
* `hyc` – scaled solution continuous
* `hyd` – scaled solution solves the scaled field

## Conclusion
* an orbit solution reaches the scaled state at the clock

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems, 2017.
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

/-- A solution `y` of `ẏ = g(y) f(y)` on `[0, t]` ends where a solution of `ẋ = f(x)` from `y 0`
is at time `∫₀ᵗ g(y)`. -/
theorem scaledSolution_unscale {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {g : X → ℝ}
    (hg : Continuous g) {y : ℝ → X} {t : ℝ} (ht : 0 ≤ t) (hy0 : ∀ u ∈ Icc 0 t, 0 ≤ g (y u))
    (hyc : ContinuousOn y (Icc 0 t))
    (hyd : ∀ u ∈ Ico 0 t, HasDerivWithinAt y (g (y u) • f (y u)) (Ici u) u) : -- --- CONCL ---
    ∃ γ : ℝ → X, γ 0 = y 0 ∧ (∀ u ∈ Icc 0 (∫ v in (0 : ℝ)..t, g (y v)),
      HasDerivAt γ (f (γ u)) u) ∧ γ (∫ v in (0 : ℝ)..t, g (y v)) = y t := by -- --- PROOF ---
  -- the speed `c`, clamped to `[0, t]` so that it is continuous on the line
  set c : ℝ → ℝ := fun u => g (y (max 0 (min u t))) with hcdef
  have hcl : Continuous fun u : ℝ => max 0 (min u t) := by fun_prop
  have hclmem : ∀ u : ℝ, max 0 (min u t) ∈ Icc 0 t := fun u =>
    ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have hc : Continuous c :=
    hg.comp (hyc.comp_continuous hcl hclmem)
  have hc0 : ∀ u, 0 ≤ c u := fun u => hy0 _ (hclmem u)
  have hcy : ∀ u ∈ Icc 0 t, c u = g (y u) := fun u hu => by
    simp [hcdef, min_eq_left hu.2, max_eq_right hu.1]
  -- the clock `σ`, monotone and with derivative `c`
  set σ : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, c v with hσdef
  have hσ : ∀ u, HasDerivAt σ (c u) u := fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hσmono : Monotone σ := monotone_of_deriv_nonneg (fun u => (hσ u).differentiableAt)
    fun u => by rw [(hσ u).deriv]; exact hc0 u
  have hσ0 : σ 0 = 0 := by simp [hσdef]
  have hσtt : σ t = ∫ v in (0 : ℝ)..t, g (y v) :=
    intervalIntegral.integral_congr fun v hv => by
      rw [uIcc_of_le ht] at hv; exact hcy v hv
  obtain ⟨γ, hγ0, hγ⟩ := lipschitzSolution hf (y 0) (σ t)
  -- `γ ∘ σ` solves the same time-dependent ODE as `y`
  have hw : ∀ u ∈ Icc 0 t, HasDerivAt (fun v => γ (σ v)) (c u • f (γ (σ u))) u := fun u hu =>
    (hγ (σ u) ⟨by rw [← hσ0]; exact hσmono hu.1, hσmono hu.2⟩).scomp u (hσ u)
  -- the Lipschitz constant of `x ↦ c u • f x`, uniform in `u`
  obtain ⟨C, hC⟩ := ((isCompact_Icc.image_of_continuousOn hyc).image hg).bddAbove
  have hCc : ∀ u, c u ≤ C := fun u => hC ⟨y (max 0 (min u t)), ⟨_, hclmem u, rfl⟩, rfl⟩
  have hlip : ∀ u : ℝ, LipschitzWith (Real.toNNReal C * K) (fun x => c u • f x) := fun u =>
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_smul₀, Real.norm_of_nonneg (hc0 u)]
      calc c u * dist (f a) (f b) ≤ C * (K * dist a b) :=
            mul_le_mul (hCc u) (hf.dist_le_mul a b) dist_nonneg ((hc0 u).trans (hCc u))
        _ = ((Real.toNNReal C * K : ℝ≥0) : ℝ) * dist a b := by
            rw [NNReal.coe_mul, Real.coe_toNNReal _ ((hc0 0).trans (hCc 0))]; ring
  have heq := ODE_solution_unique (v := fun u x => c u • f x) (a := 0) (b := t) hlip hyc
    (fun u hu => by rw [hcy u ⟨hu.1, hu.2.le⟩]; exact hyd u hu)
    (fun u hu => (hw u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hw u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) (by simp [hσ0, hγ0])
  refine ⟨γ, hγ0, ?_, ?_⟩
  · rw [← hσtt]; exact hγ
  · rw [← hσtt]; exact (heq ⟨ht, le_rfl⟩).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
