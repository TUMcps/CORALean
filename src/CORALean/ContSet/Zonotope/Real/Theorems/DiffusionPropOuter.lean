module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionProp
public import CORALean.ContSet.Zonotope.Real.Theorems.LuenbergerUpdateOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionUpdateOuter

@[expose] public section

/-!
# The set-propagation diffusion observer holds the true state

[1, Alg. 2] run over time: a state sequence `x_k = F x_{k-1} + Q_k β_k`, `|β_k| ≤ 1` (Eq. 27 of
[1, Thm. 2] with `n_k ∈ ⟨0, Q_k⟩`), from `x_0 ∈ Z₀`, whose outputs at instant `k` meet every
node's strips at the state of the previous instant, `|Γⁱ x_{k-1} - ȳⁱ_k| ≤ rⁱ_k`, is in the
zonotope of every node at every instant (`diffusionProp`). Induction on `k` with
`aux_diffusionPropStep_outer`. The positivity of `tr(Ḡʲ Ḡʲᵀ)` of [1, Prop. 1] is assumed for the
zonotopes the run produces.

## Inputs
* `F` – dynamics matrix
* `Q` – process-noise generators per instant
* `Γ` – stacked measurement matrices
* `r` – noise radii per instant
* `yb` – outputs per instant
* `nb` – neighbour indices of each node
* `o` – reduction order
* `Z₀` – initial zonotope
* `x` – state trajectory
* `β` – process-noise coefficients per instant
* `k` – instant
* `i` – node

## Hypotheses
* `hβ` – coefficients within the unit box
* `h0` – initial state lies in `Z₀`
* `hxs` – trajectory follows the dynamics
* `hy` – outputs consistent with the trajectory
* `hα` – every neighbour trace positive

## Conclusion
* the true state lies in each node's zonotope

## References

* [1] [A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      2023.](../../../../../../references/2023/alanwar-jfi-diffusion-observers.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq N : ℕ} {p m : Fin N → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n nq N : ℕ} {p : Fin N → ℕ}

-- the strip residual as noise coefficients of the diagonal `R = diag r`
private theorem Zonotope.aux_stripCoeff {k : ℕ} (a r : Vec ℝ k)
    (h : ∀ j, |a j| ≤ r j) : -- --- CONCL ---
    ∃ γ : Vec ℝ k, (∀ j, |γ j| ≤ 1) ∧
      Matrix.diagonal r *ᵥ γ = a := by -- --- PROOF ---
  refine ⟨fun j => a j / r j, fun j => ?_, ?_⟩
  · by_cases h0 : r j = 0
    · simp [h0]
    · have hr : 0 < r j := lt_of_le_of_ne (le_trans (abs_nonneg _) (h j)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hr]
      exact (div_le_one hr).mpr (h j)
  · ext j
    simp only [mulVec_diagonal]
    by_cases h0 : r j = 0
    · have : a j = 0 := abs_nonpos_iff.mp (h0 ▸ h j)
      simp [h0, this]
    · field_simp


/-- The Luenberger update of the diffusion observer holds the next state. -/
private theorem Zonotope.aux_diffusionPropLuenberger_outer (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (Zh : Fin N → Zonotope (Vec ℝ n))
    (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1) (i : Fin N) (hx : x ∈ (Zh i).construct)
    (hy : ∀ j, |(Γ i *ᵥ x - yb i) j| ≤ r i j) : -- --- CONCL ---
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionPropLuenberger F Q Γ r yb Zh i).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, hRγ⟩ := Zonotope.aux_stripCoeff (yb i - Γ i *ᵥ x) (r i) (fun j => by
    rw [← abs_neg, Pi.sub_apply]
    simpa using hy j)
  have := Zonotope.luenbergerUpdate_outer F (Γ i)
    (Zonotope.luenbergerGain F (Γ i) (Matrix.diagonal (r i)) (Zh i)) Q (Matrix.diagonal (r i))
    (yb i) (Zh i) x hx β hβ γ hγ
  rw [hRγ, sub_self, mulVec_zero, add_zero] at this
  unfold Zonotope.diffusionPropLuenberger
  exact this

end


/-- One instant of the set-propagation diffusion observer holds the next state. -/
private theorem Zonotope.aux_diffusionPropStep_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n)
    (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1)
    (hx : ∀ i, x ∈ (Zh i).construct) (hy : ∀ i j, |(Γ i *ᵥ x - yb i) j| ≤ r i j)
    (hα : ∀ i a, 0 < ∑ s, ∑ l,
      ((Zonotope.diffusionPropLuenberger F Q Γ r yb Zh (nb i a)).G l s) ^ 2) (i : Fin N)
    : -- --- CONCL ---
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionPropStep F Q Γ r yb nb o Zh i).construct := by -- --- PROOF ---
  unfold Zonotope.diffusionPropStep
  exact Zonotope.diffusionUpdate_outer o _ (hα i) (Set.mem_iInter.mpr fun a =>
    Zonotope.aux_diffusionPropLuenberger_outer F Q Γ r yb Zh x β hβ (nb i a) (hx (nb i a))
      (hy (nb i a)))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionProp_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) (x : ℕ → Vec ℝ n) (β : ℕ → Vec ℝ nq)
    (hβ : ∀ k j, |β k j| ≤ 1) (h0 : x 0 ∈ Z₀.construct)
    (hxs : ∀ k, x (k + 1) = F *ᵥ x k + Q (k + 1) *ᵥ β (k + 1))
    (hy : ∀ k i j, |(Γ i *ᵥ x k - yb (k + 1) i) j| ≤ r (k + 1) i j)
    (hα : ∀ k i a, 0 < ∑ s, ∑ l, ((Zonotope.diffusionPropLuenberger F (Q (k + 1)) Γ (r (k + 1))
      (yb (k + 1)) (Zonotope.diffusionProp F Q Γ r yb nb o Z₀ k) (nb i a)).G l s) ^ 2)
    (k : ℕ) (i : Fin N) : -- --- CONCL ---
    x k ∈ (Zonotope.diffusionProp F Q Γ r yb nb o Z₀ k i).construct := by -- --- PROOF ---
  induction k generalizing i with
  | zero => exact h0
  | succ k ih =>
    rw [hxs k]
    exact Zonotope.aux_diffusionPropStep_outer F (Q (k + 1)) Γ (r (k + 1)) (yb (k + 1)) nb o _ (x k)
      (β (k + 1)) (hβ (k + 1)) ih (hy k) (hα k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
