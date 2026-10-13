import CORALean.ContDynamics.LinearSysDT.Operations.ObserveDescriptorLPV
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntersectDescriptorHdOuter
import CORALean.ContSet.Zonotope.Real.Theorems.IntersectDescriptorLPVEq

/-!
# The descriptor LPV estimator holds the true state

[1, Alg. 1] encloses every run: if `TE + NC = I` [1, Lemma 1], the weights sum to `1` [1, Eq. 2],
the reduction is outer and `x₀ ∈ X₀`, then every run of
`E x_{k+1} = A(θ_k) x_k + B(θ_k) u_k + D(θ_k) d_k`, `y_k = C x_k + F d_k`, `d_k ∈ ⟨0, H_d⟩`
[1, Eq. 1], with `A(θ) = Σⱼ ρⱼ(θ) Aⱼ` and `B`, `D` alike, lies in `X̂_k` at every step, for any
vertex gains `Λᵢ`. By induction: [1, Thm. 1] (`intersectDescriptorHd_outer`) at the scheduled
matrices, which [1, Cor. 1] (`intersectDescriptorLPV_eq`) turns into the zonotope of line 7.

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
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

variable {n nu ny nd m r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeDescriptorLPV_outer (E T : Mat ℝ n n) (N : Mat ℝ n ny)
    (C : Mat ℝ ny n) (F : Mat ℝ ny nd) (Hd : Mat ℝ nd m) (A : Fin r → Mat ℝ n n)
    (B : Fin r → Mat ℝ n nu) (D : Fin r → Mat ℝ n nd) (Λ : Fin r → Mat ℝ n ny)
    (ρ : ℕ → Fin r → ℝ) (red : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n))
    (X₀ : Zonotope (Vec ℝ n)) (u : ℕ → Vec ℝ nu) (y : ℕ → Vec ℝ ny) (x : ℕ → Vec ℝ n)
    (b : ℕ → Vec ℝ m) (hTN : T * E + N * C = 1) (hρ : ∀ k, ∑ i, ρ k i = 1)
    (hred : ∀ Z, Z.construct ⊆ (red Z).construct) (h0 : x 0 ∈ X₀.construct)
    (hb : ∀ k i, |b k i| ≤ 1)
    (hstep : ∀ k, E *ᵥ x (k + 1) = (∑ j, ρ k j • A j) *ᵥ x k + (∑ j, ρ k j • B j) *ᵥ u k +
      (∑ j, ρ k j • D j) *ᵥ (Hd *ᵥ b k))
    (hy : ∀ k, y k = C *ᵥ x k + F *ᵥ (Hd *ᵥ b k)) (k : ℕ) :
    x k ∈ (LinearSysDT.observeDescriptorLPV T N C F Hd A B D Λ ρ red X₀ u y
      k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact h0
  | succ k ih =>
    -- [1, Thm. 1] at the scheduled matrices, then [1, Cor. 1]
    show x (k + 1) ∈ ((red (LinearSysDT.observeDescriptorLPV T N C F Hd A B D Λ ρ red X₀ u y
      k)).intersectDescriptorLPV T N (ρ k) Λ A B D C F Hd (u k) (y (k + 1))).construct
    rw [Zonotope.intersectDescriptorLPV_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (hρ k)]
    refine LinearSysDT.intersectDescriptorHd_outer E T _ N _ _ _ C F Hd (u k) (y (k + 1)) _ hTN
      ⟨⟨x k, hred _ ih, b k, hb k, ?_⟩, b (k + 1), hb (k + 1), ?_⟩
    · rw [hstep]; abel
    · rw [hy]; abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
