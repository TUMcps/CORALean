module

public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.ContSet.Zonotope.Real.Operations.FaultObserve
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The P-radius of the fault-detection observer's zonotope

[1, Eq. 14] asks `ℓ_{k+1} ≤ γ ℓ_k + ε` of the P-radius `ℓ_k = max_b ‖H_k b‖²_P` [1, Eq. 13], with
`ε = max_{s₁} ‖D_xH_w s₁‖²₂ + max_{s₂} ‖D_yH_v s₂‖²₂` [1, Eq. 15]. If the step inequality holds
for all `θ, s₁, s₂` ([1, Eq. 16, 17], `LinearSysDT.quadForm_le_of_faultRadiusLmi`), then the
zonotope of [1, Eq. 10] (`Zonotope.faultObserve`) has P-radius at most `γ ℓ + ε` for every bound
`ℓ` of the P-radius of `X`, the zonotope **after** the reduction `↓_q`: a point of the new
zonotope is its center plus `(A - LC)θ + D_xH_w s₁ - L D_yH_v s₂`, `p + θ` a point of `X`. `θ`
ranges over `↓_q(H_k)`'s span and the reduction can enlarge the P-radius, so `ℓ_k` has to be read
as `↓_q(H_k)`'s; as printed it fails (`Zonotope.faultObserve_pRadius_counterexample`).

## Inputs
* `A` – state matrix
* `B` – input matrix
* `C` – output matrix
* `L` – observer gain
* `Dx` – disturbance matrix
* `Hw` – disturbance generator matrix
* `Dy` – noise matrix
* `Hv` – noise generator matrix
* `u` – control input
* `y` – measured output
* `X` – state zonotope
* `P` – weight matrix
* `γ` – contraction rate
* `ℓ` – bound on the P-radius of `X`
* `ψw` – bound on the disturbance term
* `ψv` – bound on the noise term

## Hypotheses
* `hJ` – contraction inequality holds
* `hγ` – rate nonnegative
* `hℓ` – `X` has P-radius at most `ℓ`
* `hψw` – disturbance term bounded by `ψw`
* `hψv` – noise term bounded by `ψv`

## Conclusion
* the next P-radius is at most `γ ℓ + ψw + ψv`

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu ny nw nv rw rv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.faultObserve_pRadius_le (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (L : Mat ℝ n ny) (Dx : Mat ℝ n nw) (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (P : Mat ℝ n n) (γ ℓ ψw ψv : ℝ)
    (hJ : ∀ (θ : Vec ℝ n) (s₁ : Vec ℝ rw) (s₂ : Vec ℝ rv),
      let e := (A - L * C) *ᵥ θ + (Dx * Hw) *ᵥ s₁ - (L * (Dy * Hv)) *ᵥ s₂
      e ⬝ᵥ (P *ᵥ e) ≤ γ * (θ ⬝ᵥ (P *ᵥ θ)) + ((Dx * Hw) *ᵥ s₁) ⬝ᵥ ((Dx * Hw) *ᵥ s₁) +
        ((Dy * Hv) *ᵥ s₂) ⬝ᵥ ((Dy * Hv) *ᵥ s₂))
    (hγ : 0 ≤ γ) (hℓ : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c)) ≤ ℓ)
    (hψw : ∀ s : Vec ℝ rw, (∀ i, |s i| ≤ 1) → ((Dx * Hw) *ᵥ s) ⬝ᵥ ((Dx * Hw) *ᵥ s) ≤ ψw)
    (hψv : ∀ s : Vec ℝ rv, (∀ i, |s i| ≤ 1) → ((Dy * Hv) *ᵥ s) ⬝ᵥ ((Dy * Hv) *ᵥ s) ≤ ψv)
    : -- --- CONCL ---
    (X.faultObserve A B C L Dx Hw Dy Hv u y).pRadius P ≤ γ * ℓ + ψw + ψv := by -- --- PROOF ---
  set Z := X.faultObserve A B C L Dx Hw Dy Hv u y
  refine csSup_le ⟨_, Z.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, ⟨b, hb, rfl⟩, rfl⟩
  -- the coefficients of `X`, of `⟨0, H_w⟩` and of `⟨0, H_v⟩`
  set β : Fin X.h → ℝ := fun j => b (Fin.castAdd rv (Fin.castAdd rw j))
  set s₁ : Vec ℝ rw := fun j => b (Fin.castAdd rv (Fin.natAdd X.h j))
  set s₂ : Vec ℝ rv := fun j => b (Fin.natAdd (X.h + rw) j)
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  have hoff : (∑ j : Fin (X.h + rw + rv), b j • Z.G j) =
      (A - L * C) *ᵥ θ + (Dx * Hw) *ᵥ s₁ - (L * (Dy * Hv)) *ᵥ s₂ := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Z, Zonotope.faultObserve, Fin.append_left, Fin.append_right]
    have h1 : ∑ j, β j • ((A - L * C) *ᵥ X.G j) = (A - L * C) *ᵥ θ := by
      simp only [θ, mulVec_sum, mulVec_smul]
    have h2 : ∑ j, s₁ j • (fun i => (Dx * Hw) i j) = (Dx * Hw) *ᵥ s₁ := by
      ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
    have h3 : ∑ j, s₂ j • (fun i => -(L * Dy * Hv) i j) = -((L * (Dy * Hv)) *ᵥ s₂) := by
      ext i; simp [Matrix.mulVec, dotProduct, mul_comm, Matrix.mul_assoc]
    simp only [β, s₁, s₂] at h1 h2 h3
    rw [h1, h2, h3, sub_eq_add_neg]
    rfl
  have hoff' : (∑ j, b j • Z.G j) =
      (A - L * C) *ᵥ θ + (Dx * Hw) *ᵥ s₁ - (L * (Dy * Hv)) *ᵥ s₂ := hoff
  -- the bounds of [1, Eq. 13] and [1, Eq. 15]
  have hθ : θ ⬝ᵥ (P *ᵥ θ) ≤ ℓ := by
    have := hℓ (X.c + θ) ⟨β, fun j => hb _, rfl⟩
    rwa [add_sub_cancel_left] at this
  have hw := hψw s₁ fun j => hb _
  have hv := hψv s₂ fun j => hb _
  beta_reduce
  rw [add_sub_cancel_left, hoff']
  calc _ ≤ γ * (θ ⬝ᵥ (P *ᵥ θ)) + ((Dx * Hw) *ᵥ s₁) ⬝ᵥ ((Dx * Hw) *ᵥ s₁) +
        ((Dy * Hv) *ᵥ s₂) ⬝ᵥ ((Dy * Hv) *ᵥ s₂) := hJ θ s₁ s₂
    _ ≤ γ * ℓ + ψw + ψv := by gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
