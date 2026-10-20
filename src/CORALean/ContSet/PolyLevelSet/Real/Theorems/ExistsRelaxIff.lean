module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemRelaxIff
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A relaxed system of equations, its fresh variables bounded

With `=` in every row and the fresh variables in `[-1, 1]`, the relaxed set is the original
rows met to within `|sᵢ|`: `yᵢ = -(A μ_R(x) - b)ᵢ / sᵢ` is a slack in `[-1, 1]` exactly when
the row is off by at most `|sᵢ|`, and `0` where `sᵢ = 0` and the row is met.

## Inputs
* `P` – polynomial level set
* `s` – row slack coefficients
* `x` – point

## Hypotheses
* `h` – all rows are equations

## Conclusion
* `x` extends to the relaxed set iff each row is off by at most `|sᵢ|`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Some slack in `[-1, 1]ᵐ` completes `x` to a point of the relaxed equations exactly when `x`
is in `P`'s box and every row of `x` is met to within `|sᵢ|`. -/
theorem PolyLevelSet.exists_relax_iff {P : PolyLevelSet n} (h : ∀ i, P.op i = .eq)
    (s : Vec ℝ P.m) (x : Vec ℝ n) : -- --- CONCL ---
    (∃ y : Vec ℝ P.m, Fin.append x y ∈ (P.relax s (Interval.unit P.m)).construct)
      ↔ x ∈ P.dom.construct ∧ ∀ i, |P.eval x i| ≤ |s i| := by -- --- PROOF ---
  have key : ∀ y : Vec ℝ P.m, Fin.append x y ∈ (P.relax s (Interval.unit P.m)).construct
      ↔ (x ∈ P.dom.construct ∧ ∀ i, |y i| ≤ 1) ∧ ∀ i, P.eval x i + s i * y i = 0 := by
    intro y
    rw [PolyLevelSet.mem_relax_iff, Interval.mem_unit_iff]
    simp only [Fin.append_left, Fin.append_right]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [h i]
    rfl
  constructor
  · rintro ⟨y, hmem⟩
    obtain ⟨⟨hx, hy⟩, hrows⟩ := (key y).mp hmem
    refine ⟨hx, fun i => ?_⟩
    -- the row is off by `sᵢ yᵢ`, and `|yᵢ| ≤ 1`
    have hrow : P.eval x i = -(s i * y i) := by
      linarith [hrows i]
    rw [hrow, abs_neg, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hy i)
  · rintro ⟨hx, hs⟩
    -- the slack each row needs, `0` on a row with no room
    refine ⟨fun i => if s i = 0 then 0 else -P.eval x i / s i,
      (key _).mpr ⟨⟨hx, fun i => ?_⟩, fun i => ?_⟩⟩
    · by_cases h0 : s i = 0
      · simp [h0]
      · simp only [if_neg h0, abs_div]
        rw [div_le_one (abs_pos.mpr h0), abs_neg]
        exact hs i
    · by_cases h0 : s i = 0
      · have h' : P.eval x i = 0 := by simpa [h0] using hs i
        simp only [if_pos h0, mul_zero, add_zero]
        exact h'
      · simp only [if_neg h0]
        rw [mul_div_cancel₀ _ h0]
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
