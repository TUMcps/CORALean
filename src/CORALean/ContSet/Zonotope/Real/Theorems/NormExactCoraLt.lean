import CORALean.ContSet.Zonotope.Real.Operations.NormExactCora
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

/-!
# CORA's `norm(Z,2,'exact')` under-estimates the largest norm

For `Z = zonotope([2;-20],[1 1;0 1])`, `‖G u‖²` over `u ∈ {-1, 1}²` is `5` at `±(1, 1)` and `1`
otherwise, so every minimiser of CORA's binary program gives `x = (4, -19)` or `x = (0, -21)`,
`‖x‖ = √377` or `√441`. The point `(2, -21) = c + G (1, -1)` of `Z` has norm `√445`, the true
maximum: whatever solver and `λ` CORA uses, `Zonotope.normExactCora` is strictly below it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.normExactCora_lt :
    let Z : Zonotope (Vec ℝ 2) := ⟨2, ![(2 : ℝ), -20], ![![1, 0], ![1, 1]]⟩
    ![(2 : ℝ), -21] ∈ Z.construct ∧
      ∀ (lmax : ℝ) (binprog : ((Fin Z.h → Bool) → ℝ) → (Fin Z.h → Bool)),
        (∀ (f : (Fin Z.h → Bool) → ℝ) b, f (binprog f) ≤ f b) →
          Z.normExactCora lmax binprog < ‖![(2 : ℝ), -21]‖₂ := by -- --- PROOF ---
  intro Z
  -- `(2, -21) = c + G (1, -1)`; CORA's objective, as `normExactCora` unfolds it
  refine ⟨⟨![1, -1], fun j => ?_, ?_⟩, fun lmax binprog hopt => ?_⟩
  · fin_cases j <;> simp
  · funext i
    fin_cases i <;> simp [Z, Fin.sum_univ_two]
    norm_num
  · let half : (Fin 2 → Bool) → Vec ℝ 2 := fun b j => (if b j then 1 else 0) - 1 / 2
    let obj : (Fin 2 → Bool) → ℝ := fun b => 4 * (half b ⬝ᵥ
      ((lmax • (1 : Mat ℝ 2 2) - Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) *ᵥ half b))
    have hle : ∀ b', obj (binprog obj) ≤ obj b' := hopt obj
    change ‖∑ j, (2 * half (binprog obj) j) • Z.G j + Z.c‖₂ < _
    generalize binprog obj = s at hle ⊢
    -- `obj = 2λ - ‖G u‖²`: `2λ - 5` at `±(1, 1)`, `2λ - 1` at the others, so `s` is constant
    have htt := hle fun _ => true
    have hff := hle fun _ => false
    rw [norm₂, norm₂]
    apply Real.sqrt_lt_sqrt (by positivity)
    cases h0 : s 0 <;> cases h1 : s 1 <;>
      simp [obj, half, Z, dotProduct, mulVec, Fin.sum_univ_two, h0, h1] at htt hff ⊢ <;>
      norm_num at htt hff ⊢
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
