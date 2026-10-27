module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStrip
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionUpdateOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter

@[expose] public section

/-!
# The strip-based diffusion observer holds the true state

[1, Alg. 1] run over time: a state sequence `x_{k+1} = F x_k + Q_k β_k`, `|β_k| ≤ 1` (the system
of Eq. 8 of [1] with `n_k ∈ ⟨0, Q_k⟩`), from `x_0 ∈ Z₀`, whose outputs meet every node's strips
`|Γⁱ x_k - ȳⁱ_k| ≤ rⁱ_k` at every instant, is in the predicted zonotope of every node at every
instant (`diffusionStrip`). Induction on `k` with `aux_diffusionStripStep_outer`. The positivity of
`tr(Ḡʲ Ḡʲᵀ)` of [1, Prop. 1] is assumed for the zonotopes the run produces.

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
* the true state lies in each node's predicted zonotope

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
variable {n nq : ℕ}

/-- The time update of the diffusion observers encloses the next state. -/
private theorem Zonotope.aux_diffusionTimeUpdate_outer (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Zt : Zonotope (Vec ℝ n)) (x : Vec ℝ n) (hx : x ∈ Zt.construct) (β : Vec ℝ nq)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    F *ᵥ x + Q *ᵥ β ∈ (Zonotope.diffusionTimeUpdate F Q Zt).construct := by -- --- PROOF ---
  obtain ⟨α, hα, rfl⟩ := hx
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Fin.append α β, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [hα, hβ]
  · show _ = _ + ∑ j : Fin (Zt.h + nq), _
    rw [Fin.sum_univ_add]
    simp only [Zonotope.diffusionTimeUpdate, Fin.append_left, Fin.append_right]
    have h1 : ∑ j, α j • (F *ᵥ Zt.G j) = F *ᵥ ∑ j, α j • Zt.G j := by
      rw [mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => (mulVec_smul _ _ _).symm
    rw [h1, hcol Q β, mulVec_add]
    abel

end


/-- One instant of the strip-based diffusion observer holds the next state. -/
private theorem Zonotope.aux_diffusionStripStep_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n)
    (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1)
    (hx : ∀ i, x ∈ (Zh i).construct) (hy : ∀ i j, |(Γ i *ᵥ x - yb i) j| ≤ r i j)
    (hα : ∀ i a, 0 < ∑ s, ∑ l,
      ((Zonotope.diffusionStripMeasurement Γ r yb Zh (nb i a)).G l s) ^ 2) (i : Fin N)
    : -- --- CONCL ---
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionStripStep F Q Γ r yb nb o Zh i).construct := by -- --- PROOF ---
  unfold Zonotope.diffusionStripStep
  refine Zonotope.aux_diffusionTimeUpdate_outer F Q _ x ?_ β hβ
  refine Zonotope.diffusionUpdate_outer o _ (hα i) (Set.mem_iInter.mpr fun a => ?_)
  -- Step 1 at the neighbour: `x` meets the strips and is in the predicted zonotope
  unfold Zonotope.diffusionStripMeasurement
  exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨hx (nb i a), hy (nb i a)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionStrip_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) (x : ℕ → Vec ℝ n) (β : ℕ → Vec ℝ nq)
    (hβ : ∀ k j, |β k j| ≤ 1) (h0 : x 0 ∈ Z₀.construct)
    (hxs : ∀ k, x (k + 1) = F *ᵥ x k + Q k *ᵥ β k)
    (hy : ∀ k i j, |(Γ i *ᵥ x k - yb k i) j| ≤ r k i j)
    (hα : ∀ k i a, 0 < ∑ s, ∑ l, ((Zonotope.diffusionStripMeasurement Γ (r k) (yb k)
      (Zonotope.diffusionStrip F Q Γ r yb nb o Z₀ k) (nb i a)).G l s) ^ 2) (k : ℕ) (i : Fin N)
    : -- --- CONCL ---
    x k ∈ (Zonotope.diffusionStrip F Q Γ r yb nb o Z₀ k i).construct := by -- --- PROOF ---
  induction k generalizing i with
  | zero => exact h0
  | succ k ih =>
    rw [hxs k]
    exact Zonotope.aux_diffusionStripStep_outer F (Q k) Γ (r k) (yb k) nb o _ (x k) (β k) (hβ k)
      ih (hy k) (hα k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
