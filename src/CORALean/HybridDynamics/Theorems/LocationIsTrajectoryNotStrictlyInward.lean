module

public import CORALean.HybridDynamics.Definitions.Location
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# A stay cannot end on a hyperplane while the flow there points strictly inward

A stay of positive length `τ` inside `{y | c·y ≤ d}` that ends on `{y | c·y = d}` has not a flow
component `c·ẋ` strictly below a fixed `b < 0` for every input and disturbance the location
allows, evaluated at the end state: the end state would be reached from outside the halfspace.
Inputs and disturbances are only measurable, so `x` need not be differentiable; the argument is
the integral of the flow over a short interval before `τ`. The state `x s` before `τ` differs from
`x τ` by little (`x` is continuous), so the flow at `x s` and the input at `s` stays below `b / 2`.

## Inputs
* `ℓ` – location
* `τ` – length of the stay
* `x` – state
* `u` – input of the stay, in `U` at every time
* `w` – disturbance of the stay, in `W` at every time
* `c` – normal
* `d` – offset
* `b` – bound

## Hypotheses
* `traj` – the stay
* `hτ` – the stay has positive length
* `hinv` – the invariant lies in `c·y ≤ d`
* `hxd` – the end state is on the hyperplane
* `hb` – the bound is negative
* `hflow` – at the end state, with the input and disturbance of every time, the flow is below `b`

## Conclusion
* no such stay exists, which is `False`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSetLike Scalar MeasureTheory Set

variable {S G : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, ContSetLike (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Dotting with `c` as a continuous linear map. -/
private noncomputable def aux_dotCLM (c : Vec ℝ n) : Vec ℝ n →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

private theorem aux_dotCLM_apply (c v : Vec ℝ n) : aux_dotCLM c v = c ⬝ᵥ v := by
  simp [aux_dotCLM, dotProduct]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.IsTrajectory.not_strictly_inward
    {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ ℓ.dynamics.m}
    {w : ℝ → Vec ℝ ℓ.dynamics.r} (traj : ℓ.IsTrajectory τ x u w) (hτ : 0 < τ) (c : Vec ℝ n)
    (d : ℝ) (hinv : ∀ y ∈ toSet ℓ.inv, c ⬝ᵥ y ≤ d) (hxd : c ⬝ᵥ x τ = d) {b : ℝ} (hb : b < 0)
    (hflow : ∀ s ∈ Icc 0 τ, c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ x τ + (toRealMat ℓ.dynamics.B *ᵥ u s +
      toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s)) ≤ b) : -- --- CONCL ---
    False := by -- --- PROOF ---
  set f : ℝ → Vec ℝ n := fun s => toRealMat ℓ.dynamics.A *ᵥ x s +
    toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c +
      toRealMat ℓ.dynamics.E *ᵥ w s with hf
  have hτmem : τ ∈ Icc 0 τ := ⟨hτ.le, le_rfl⟩
  -- the term of the flow that follows the state, continuous at `τ`
  set ψ : ℝ → ℝ := fun s => c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ (x s - x τ)) with hψ
  have hψc : ContinuousOn ψ (Icc 0 τ) := by
    have h1 : Continuous fun y : Vec ℝ n => c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ (y - x τ)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact h1.comp_continuousOn traj.cont
  have hψτ : ψ τ = 0 := by simp [hψ]
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.mp (hψc τ hτmem) (-b / 2) (by linarith)
  -- a short interval before `τ`
  set η : ℝ := min τ (δ / 2) with hη
  have hη0 : 0 < η := lt_min hτ (by linarith)
  have hητ : η ≤ τ := min_le_left _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmem : ∀ s ∈ Icc (τ - η) τ, s ∈ Icc 0 τ := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  -- the flow component is below `b / 2` there
  have hg : ∀ s ∈ Icc (τ - η) τ, c ⬝ᵥ f s ≤ b / 2 := by
    intro s hs
    have hs0 := hmem s hs
    have hd : Dist.dist s τ < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]; linarith [hs.1]
    have h1 := hδψ hs0 hd
    rw [Real.dist_eq, hψτ, sub_zero] at h1
    have h2 := (abs_lt.mp h1).2
    have h3 := hflow s hs0
    have : c ⬝ᵥ f s = ψ s + c ⬝ᵥ (toRealMat ℓ.dynamics.A *ᵥ x τ + (toRealMat ℓ.dynamics.B *ᵥ u s +
        toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s)) := by
      simp only [hf, hψ, ← dotProduct_add, Matrix.mulVec_sub]
      congr 1
      abel
    rw [this]
    linarith
  -- the state at `τ` minus the state at `τ - η` is the integral of the flow between
  have hi : ∀ t ∈ Icc 0 τ, IntervalIntegrable f volume 0 t := traj.integrable
  have hiτ := hi τ hτmem
  have hint : IntervalIntegrable f volume (τ - η) τ :=
    hiτ.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le hτ.le]
      exact Icc_subset_Icc (by linarith) le_rfl)
  have hdiff : x τ - x (τ - η) = ∫ s in (τ - η)..τ, f s := by
    rw [traj.flow τ hτmem, traj.flow (τ - η) ⟨by linarith, by linarith⟩]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left hiτ
      (hi _ ⟨by linarith, by linarith⟩)]
  -- dotting with `c`
  have hdot : c ⬝ᵥ x τ - c ⬝ᵥ x (τ - η) = ∫ s in (τ - η)..τ, c ⬝ᵥ f s := by
    have := (aux_dotCLM c).intervalIntegral_comp_comm hint
    have key : (fun s => aux_dotCLM c (f s)) = fun s => c ⬝ᵥ f s :=
      funext fun s => aux_dotCLM_apply _ _
    rw [key, aux_dotCLM_apply] at this
    rw [← dotProduct_sub, hdiff, this]
  have hle : ∫ s in (τ - η)..τ, c ⬝ᵥ f s ≤ ∫ s in (τ - η)..τ, b / 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (by simp) fun s hs => hg s hs
    have h : IntervalIntegrable (fun s => aux_dotCLM c (f s)) volume (τ - η) τ :=
      ⟨(aux_dotCLM c).integrable_comp hint.1, (aux_dotCLM c).integrable_comp hint.2⟩
    have key : (fun s => aux_dotCLM c (f s)) = fun s => c ⬝ᵥ f s :=
      funext fun s => aux_dotCLM_apply _ _
    rwa [key] at h
  rw [intervalIntegral.integral_const] at hle
  simp only [smul_eq_mul] at hle
  -- the state before `τ` is outside the halfspace
  have hx0 := hinv _ (traj.invariant (τ - η) ⟨by linarith, by linarith⟩)
  nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
