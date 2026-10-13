module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntersectDescriptorOuter

@[expose] public section

/-!
# The intersection zonotope for one uncertainty driving state and output

[2, Thm. 1]: for the descriptor system `E x_k = A x_{k-1} + B u_{k-1} + D d_{k-1}`,
`y_k = C x_k + F d_k`, `d ∈ D = ⟨0, H_d⟩` [2, Eq. 1], with `TE + NC = I` [2, Lemma 1] and any
correction matrix `Λ`, the consistent set `X̄_k ∩ X_{y_k}` [2, Def. 4] of the prediction
`X̄_k = {x | E x - B u ∈ A X̂_{k-1} ⊕ D D}` [2, Def. 2] and the measurement set
`X_{y_k} = {x | y_k - C x ∈ F D}` [2, Def. 3] lies in the zonotope of its Eq. 10. The matrices
are those of the scheduling parameter `θ_{k-1}`, fixed for the step. This is [1, Thm. 1] with
`D H_d`, `F H_d` as its `D`, `F`, no unknown input, and the measurement noise sign flipped, the
box being symmetric; that Eq. 10 is Eq. 7 of [1, Thm. 1] in this notation.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
* [2] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nd m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intersectDescriptorHd_outer (E T A : Mat ℝ n n) (N Λ : Mat ℝ n ny)
    (B : Mat ℝ n nu) (D : Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nd) (Hd : Mat ℝ nd m)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (hTN : T * E + N * C = 1) :
    {x | ∃ xp ∈ X.construct, ∃ b : Vec ℝ m, (∀ i, |b i| ≤ 1) ∧
        E *ᵥ x - B *ᵥ u = A *ᵥ xp + D *ᵥ (Hd *ᵥ b)} ∩
      {x | ∃ b : Vec ℝ m, (∀ i, |b i| ≤ 1) ∧ y - C *ᵥ x = F *ᵥ (Hd *ᵥ b)} ⊆
      (X.intersectDescriptor T N Λ A B (D * Hd) C (F * Hd) u y).construct := by -- --- PROOF ---
  rintro x ⟨⟨xp, hxp, b, hb, hE⟩, b', hb', hy⟩
  -- the sets of [1, Thm. 1] at `D H_d`, `F H_d`, no unknown input, noise `-b'`
  refine LinearSysDT.intersectDescriptor_outer E T A N Λ B (D * Hd) (0 : Mat ℝ n 0) C (F * Hd)
    u y X hTN (Matrix.mul_zero T) ⟨⟨xp, hxp, b, hb, 0, ?_⟩, -b', fun i => by simpa using hb' i, ?_⟩
  · rw [zero_mulVec, add_zero, ← mulVec_mulVec, add_right_comm, ← hE]; abel
  · rw [mulVec_neg, ← mulVec_mulVec, ← hy]; abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
