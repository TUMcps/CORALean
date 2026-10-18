module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ConsistentSet
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A component of the output bounds the consistent states by a strip

[1, Property 1]: if `c`, `s` and `σ` are such that `cᵀX̄ - g_i(X̄, V) ⊆ [s - σ, s + σ]` (the paper
obtains `c = mid □∇ₓg_i(X̄, V)` and the enclosure by interval arithmetic), then `X̄ ∩ X_y(i) ⊆ X̄ ∩
{x | |cᵀx - y_i - s| ≤ σ}`. The proof is the paper's: `cᵀx - y_i = cᵀx - g_i(x, v)` lies in the
difference of the two ranges. Any `c` does, `c` being a hypothesis. The paper prints the strip's
offset as `s_i` where it first names a scalar `d_i`; `s_i` is what the proof uses.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.consistentSet_inter_subset_strip {n nv p : ℕ}
    (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p) (V : Set (Vec ℝ nv)) (y : Vec ℝ p) (i : Fin p)
    (Xbar : Set (Vec ℝ n)) (c : Vec ℝ n) (s σ : ℝ)
    (h : ∀ a ∈ (fun x => c ⬝ᵥ x) '' Xbar, ∀ b ∈ {b | ∃ x ∈ Xbar, ∃ v ∈ V, b = g x v i},
      s - σ ≤ a - b ∧ a - b ≤ s + σ) : -- --- STMT ---
    Xbar ∩ NonlinearSysDT.consistentSetComp g V y i ⊆
      Xbar ∩ {x | |c ⬝ᵥ x - y i - s| ≤ σ} := by -- --- PROOF ---
  rintro x ⟨hx, v, hv, hy⟩
  refine ⟨hx, ?_⟩
  -- `cᵀx - y_i = cᵀx - g_i(x, v)` is a difference of an element of each range
  obtain ⟨h1, h2⟩ := h (c ⬝ᵥ x) ⟨x, hx, rfl⟩ (g x v i) ⟨x, hx, v, hv, rfl⟩
  rw [← hy] at h1 h2
  show |c ⬝ᵥ x - y i - s| ≤ σ
  rw [abs_le]
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
