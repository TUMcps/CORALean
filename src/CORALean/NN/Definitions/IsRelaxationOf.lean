module

public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# A set-based network relaxes a function

`N.IsRelaxationOf Φ`: `Φ` is the network of [1, Def. 1] whose layers `N` encloses, a linear layer
`W h + b` as itself and an activation `ϕ`, applied elementwise, through slope `m` and errors `e`,
`ē` that are approximation errors in the sense of [2, Def. 6]: on every value `t` a row `H` of the
input set takes, `e(H) ≤ ϕ(t) - m(H) t ≤ ē(H)`. That is pointwise, not only the set-level
`L_k(H) ⊆ enclose(L_k, H)` of [1, Prop. 1], and it is what keeps the input's factors in the output
(`SetBasedNet.forward_latent`, the latent space of [1, Sec. 3]), on which [1, Prop. 2] rests.

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../references/2026/koller-iclr-latent-space.md)
* [2] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ========================================  MAIN TYPE  ========================================= --

/-- `Φ` is the network `N` encloses, each activation's errors bounding `ϕ(t) - m t` pointwise. -/
inductive SetBasedNet.IsRelaxationOf :
    ∀ {n k : ℕ}, SetBasedNet n k → (Vec ℝ n → Vec ℝ k) → Prop where
  | output {n : ℕ} : IsRelaxationOf (.output : SetBasedNet n n) id
  | linear {n m k : ℕ} {W : Mat ℝ m n} {b : Vec ℝ m} {tail : SetBasedNet m k}
      {Φ : Vec ℝ m → Vec ℝ k} (h : IsRelaxationOf tail Φ) :
      IsRelaxationOf (.linear W b tail) (fun x => Φ (W *ᵥ x + b))
  | nonlinear {n k : ℕ} (ϕ : ℝ → ℝ) {m eLo eUp : Zonotope (Vec ℝ 1) → ℝ}
      {tail : SetBasedNet n k} {Φ : Vec ℝ n → Vec ℝ k}
      (hϕ : ∀ (H : Zonotope (Vec ℝ 1)) (t : ℝ), (fun _ => t) ∈ H.construct →
        eLo H ≤ ϕ t - m H * t ∧ ϕ t - m H * t ≤ eUp H)
      (h : IsRelaxationOf tail Φ) :
      IsRelaxationOf (.nonlinear m eLo eUp tail) (fun x => Φ (fun i => ϕ (x i)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
