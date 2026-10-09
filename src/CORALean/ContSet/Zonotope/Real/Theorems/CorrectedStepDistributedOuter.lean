import CORALean.ContSet.Zonotope.Real.Operations.CorrectedStepDistributed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# The distributed zonotope holds the agent's next state

[1, Prop. 1]: if every neighbour `j ∈ N_i` has `x_j(k-1) ∈ ⟨c_j(k-1), H_j(k-1)⟩`, then for every
correction matrix `Λ_i`, `x_i(k) ∈ ⟨c_i(k), H_i(k)⟩` Eq. 6 of [1, Prop. 1], with `c_i` and `H_i`
as in Eq. 7. As in the paper's proof: each neighbour has its own coefficient vector `θ_j`, so
`x_i(k) = Σ_j A_ij (c_j + H_j θ_j) + B_i u_i + D_{w_i} ϖ_i`, the stacked `θ`'s and `ϖ_i` being the
`η_i` of the proof; adding `Λ_i(y_i(k) - C_i x_i(k) - D_{v_i} σ_i) = 0` leaves `x_i(k)` at the point
with coefficients `(η_i, -σ_i)`. The disturbance `D_{w_i}` has `n_i` rows, `w_i` entering the state;
the paper prints it `m_{w_i} × m_{w_i}`, which fits only when it is square.

## References

* [1] Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". IEEE Conference on Decision and Control (CDC),
      pp. 668-673, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv q : ℕ} {m : Fin q → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.correctedStepDistributed_outer (Λ : Mat ℝ n ny) (A : ∀ a, Mat ℝ n (m a))
    (B : Mat ℝ n nu) (Dw : Mat ℝ n nw) (C : Mat ℝ ny n) (Dv : Mat ℝ ny nv) (u : Vec ℝ nu)
    (y : Vec ℝ ny) (X : ∀ a, Zonotope (Vec ℝ (m a))) (x : ∀ a, Vec ℝ (m a))
    (hx : ∀ a, x a ∈ (X a).construct) (ϖ : Vec ℝ nw) (hϖ : ∀ j, |ϖ j| ≤ 1) (σ : Vec ℝ nv)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hy : y = C *ᵥ (∑ a, A a *ᵥ x a + B *ᵥ u + Dw *ᵥ ϖ) + Dv *ᵥ σ) :
    ∑ a, A a *ᵥ x a + B *ᵥ u + Dw *ᵥ ϖ ∈
      (Zonotope.correctedStepDistributed Λ A B Dw C Dv u y X).construct := by -- --- PROOF ---
  choose β hβ hxa using hx
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  -- the neighbours' offsets `θ_a`, stacked over the sigma type, and the state to be enclosed
  set θ : Vec ℝ n := ∑ a, A a *ᵥ ∑ j, β a j • (X a).G j with hθ
  set x' : Vec ℝ n := ∑ a, A a *ᵥ x a + B *ᵥ u + Dw *ᵥ ϖ with hx'
  set β' : Fin (∑ a, (X a).h) → ℝ := fun k => β (finSigmaFinEquiv.symm k).1
    (finSigmaFinEquiv.symm k).2 with hβ'
  -- the coefficients: the neighbours', the disturbance's and the noise's
  refine ⟨Fin.append (Fin.append β' ϖ) (fun j => -σ j), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) (fun j => ?_) j <;>
      simp [hβ', hβ, hϖ, hσ]
  · show x' = _ + ∑ j : Fin ((∑ a, (X a).h) + nw + nv), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.correctedStepDistributed, Fin.append_left, Fin.append_right]
    -- the neighbours' block, summed over the sigma type
    have hA : ∑ k : Fin (∑ a, (X a).h), β' k • ((1 - Λ * C) *ᵥ (A (finSigmaFinEquiv.symm k).1 *ᵥ
        (X (finSigmaFinEquiv.symm k).1).G (finSigmaFinEquiv.symm k).2)) =
        (1 - Λ * C) *ᵥ θ := by
      rw [Equiv.sum_comp finSigmaFinEquiv.symm
        (fun s : (Σ a, Fin (X a).h) => β s.1 s.2 • ((1 - Λ * C) *ᵥ (A s.1 *ᵥ (X s.1).G s.2))),
        Fintype.sum_sigma]
      simp only [hθ, mulVec_sum, mulVec_smul]
    -- the last block is `-Λ D_v σ`
    have h3 : ∑ j, (-σ j) • (fun i => (Λ * Dv) i j) = -((Λ * Dv) *ᵥ σ) := by
      rw [← mulVec_neg, ← hcol]; rfl
    rw [hA, hcol, h3]
    -- the correction `Λ(y - C x - D_v σ) = 0`, added to the prediction
    have hK : ∀ w, (1 - Λ * C) *ᵥ w = w - Λ *ᵥ (C *ᵥ w) := fun w => by
      simp [sub_mulVec, mulVec_mulVec]
    have hΛ : Λ *ᵥ y = Λ *ᵥ (C *ᵥ x') + (Λ * Dv) *ᵥ σ := by
      rw [hy, mulVec_add, ← mulVec_mulVec]
    rw [hΛ]
    -- every neighbour's state is its centre plus its offset
    have hxs : ∑ a, A a *ᵥ x a = ∑ a, A a *ᵥ (X a).c + θ := by
      rw [hθ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hxa a, mulVec_add]
    -- the state as the centre, its offset and the disturbance
    have hxe : x' = (∑ a, A a *ᵥ (X a).c + B *ᵥ u) + θ + Dw *ᵥ ϖ := by
      rw [hx', hxs]; abel
    have key : (1 - Λ * C) *ᵥ (∑ a, A a *ᵥ (X a).c + B *ᵥ u) + (1 - Λ * C) *ᵥ θ +
        ((1 - Λ * C) * Dw) *ᵥ ϖ = (1 - Λ * C) *ᵥ x' := by
      rw [hxe]; simp only [mulVec_add, mulVec_mulVec]
    -- what is left is `x' = (I - ΛC) x' + Λ C x'`
    have e1 : (1 - Λ * C) *ᵥ (∑ a, A a *ᵥ (X a).c + B *ᵥ u) + (Λ *ᵥ C *ᵥ x' + (Λ * Dv) *ᵥ σ) +
        ((1 - Λ * C) *ᵥ θ + ((1 - Λ * C) * Dw) *ᵥ ϖ + -((Λ * Dv) *ᵥ σ)) =
        ((1 - Λ * C) *ᵥ (∑ a, A a *ᵥ (X a).c + B *ᵥ u) + (1 - Λ * C) *ᵥ θ +
          ((1 - Λ * C) * Dw) *ᵥ ϖ) + Λ *ᵥ C *ᵥ x' := by abel
    rw [e1, key, hK]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
