module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Operations.ObserveDescriptor
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The prediction-type zonotopic observer holds the true state

[1, Thm. 5]: with `TE + NC = I` and `TD_d = 0` [1, Eq. 6], a state `x ∈ ⟨p̂, H̄⟩`, the outputs `y =
C x + F υ` and `y₊ = C x₊ + F υ₊`, and `E x₊ = A x + B u + D ω + D_d d` [1, Eq. 4] with `ω`, `υ`,
`υ₊` in the unit box and `d` anything, put `x₊` in `⟨p̂₊(G), Ĥ₊(G)⟩` Eq. 31 of [1, Thm. 5], for
every gain `G`. As in the paper's proof, which sets `x̂ = x` in Eq. 30 of [1, Thm. 5]: then `G(y - C
x - F υ) = 0` and `x₊ = (TE + NC) x₊ = TA x + TB u + TD ω + N y₊ - NF υ₊`, the point of the zonotope
at the coefficients `(β, ω, υ₊, υ)`.

## Inputs
* `E` – descriptor matrix
* `T` – decoupling matrix
* `A` – state matrix
* `N` – measurement decoupling matrix
* `G` – observer gain
* `B` – input matrix
* `D` – disturbance matrix
* `Dd` – unknown input matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – input at this step
* `X` – previous zonotope
* `x` – state
* `x_plus` – next state
* `ω` – disturbance coefficients
* `υ` – noise coefficients
* `υ_plus` – next noise coefficients
* `d` – unknown input

## Hypotheses
* `hTN` – decoupling identity holds
* `hTD` – decoupling kills the unknown input
* `hx` – `x` lies in `X`
* `hω` – disturbance coefficients within one
* `hυ` – noise coefficients within one
* `hυp` – next noise coefficients within one
* `hE` – the descriptor step holds

## Conclusion
* the next state lies in the observer zonotope

## References

* [1] [Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica,
      2018.](../../../../../../references/2018/wang-automatica-descriptor-observer.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu nw nd ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeDescriptor_outer (E T A : Mat ℝ n n) (N G : Mat ℝ n ny)
    (B : Mat ℝ n nu) (D : Mat ℝ n nw) (Dd : Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (X : Zonotope (Vec ℝ n)) (hTN : T * E + N * C = 1) (hTD : T * Dd = 0)
    (x x_plus : Vec ℝ n) (ω : Vec ℝ nw) (υ υ_plus : Vec ℝ nv) (d : Vec ℝ nd)
    (hx : x ∈ X.construct) (hω : ∀ i, |ω i| ≤ 1) (hυ : ∀ i, |υ i| ≤ 1)
    (hυp : ∀ i, |υ_plus i| ≤ 1)
    (hE : E *ᵥ x_plus = A *ᵥ x + B *ᵥ u + D *ᵥ ω + Dd *ᵥ d) : -- --- CONCL ---
    x_plus ∈ (X.observeDescriptor T N G A B D C F u (C *ᵥ x + F *ᵥ υ)
      (C *ᵥ x_plus + F *ᵥ υ_plus)).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  -- a matrix's columns weighted by a vector are the matrix times it
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  have hcolneg : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k),
      ∑ j, v j • (fun i => -M i j) = -(M *ᵥ v) := fun M v => by
    ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  -- the next state, the unknown input decoupled
  have hxp : x_plus = T *ᵥ (A *ᵥ (X.c + θ)) + T *ᵥ (B *ᵥ u) + T *ᵥ (D *ᵥ ω) +
      N *ᵥ (C *ᵥ x_plus) := by
    have h1 : x_plus = T *ᵥ (E *ᵥ x_plus) + N *ᵥ (C *ᵥ x_plus) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, hTN, one_mulVec]
    have hd : T *ᵥ (Dd *ᵥ d) = 0 := by rw [mulVec_mulVec, hTD, zero_mulVec]
    conv_lhs => rw [h1]
    rw [hE]
    simp only [mulVec_add, hd, add_zero]
  refine ⟨Fin.append (Fin.append (Fin.append β ω) υ_plus) υ, ?_, ?_⟩
  · -- every coefficient is in `[-1, 1]`
    intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_)
      (fun j => ?_) j) (fun j => ?_) j) (fun j => ?_) j <;> simp [hβ, hω, hυ, hυp]
  · -- the four generator blocks summed
    show x_plus = _ + ∑ j : Fin (X.h + nw + nv + nv), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.observeDescriptor, Fin.append_left, Fin.append_right]
    have hX : ∑ j, β j • ((T * A - G * C) *ᵥ X.G j) = (T * A - G * C) *ᵥ θ := by
      simp only [θ, mulVec_sum, mulVec_smul]
    rw [hX, hcol, hcolneg, hcolneg]
    -- `(TA - GC)(p̂ + θ) + G(C x + F υ) = TA x + GF υ`, and the rest is `x₊`
    conv_lhs => rw [hxp]
    simp only [sub_mulVec, ← mulVec_mulVec, mulVec_add]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
