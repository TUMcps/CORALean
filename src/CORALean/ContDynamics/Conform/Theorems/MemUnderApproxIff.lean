module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Abel
public import CORALean.Global.Tensor

@[expose] public section

/-!
# [1, Eq. 5]: subtracting the nominal solution

[1, Eq. 2]-[1, Eq. 3] give the output set at `h` as `C(e^{Ah}(x₀ ⊕ X̃₀) ⊕ ∫ e^{A(h-τ)} B u(τ) dτ
⊕ Υ W_c) ⊕ V`, and the nominal output as `ỹ = C(e^{Ah} x₀ + ∫ e^{A(h-τ)} B u(τ) dτ)`. Then
`y` lies in the first iff `y - ỹ ∈ C(e^{Ah} X̃₀ ⊕ Υ W_c) ⊕ V`, independent of `x₀` and `u`.
The exponential, the input integral and `Υ` enter only as a matrix `Φ`, a vector `b` and
a matrix `Υ`, so the statement is made for any of these: nothing else is used.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5]: `y` is in the output set iff its deviation from `ỹ` is in the shifted one. -/
theorem Conform.mem_underApprox_iff {n m : ℕ} (C : Mat ℝ m n) (Φ Υ : Mat ℝ n n)
    (x0 b : Vec ℝ n) (X0 Wc : Set (Vec ℝ n)) (V : Set (Vec ℝ m)) (y : Vec ℝ m) :
    y ∈ (fun x => C *ᵥ x) '' ((fun x => Φ *ᵥ x) '' ({x0} + X0) + {b}
        + (fun w => Υ *ᵥ w) '' Wc) + V ↔
      y - C *ᵥ (Φ *ᵥ x0 + b) ∈ (fun x => C *ᵥ x) '' ((fun x => Φ *ᵥ x) '' X0
        + (fun w => Υ *ᵥ w) '' Wc) + V := by -- --- PROOF ---
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, rfl, xt, hxt, rfl⟩, rfl⟩, _, rfl, rfl⟩, _, ⟨w, hw, rfl⟩,
      rfl⟩, rfl⟩, v, hv, rfl⟩
    refine ⟨_, ⟨_, ⟨_, ⟨xt, hxt, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩, v, hv, ?_⟩
    simp only [mulVec_add]
    abel
  · rintro ⟨_, ⟨_, ⟨_, ⟨xt, hxt, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩, v, hv, hy⟩
    refine ⟨_, ⟨_, ⟨_, ⟨_, ⟨x0 + xt, ⟨x0, rfl, xt, hxt, rfl⟩, rfl⟩, b, rfl, rfl⟩, _,
      ⟨w, hw, rfl⟩, rfl⟩, rfl⟩, v, hv, ?_⟩
    simp only [mulVec_add] at hy ⊢
    rw [eq_sub_iff_add_eq] at hy
    rw [← hy]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
