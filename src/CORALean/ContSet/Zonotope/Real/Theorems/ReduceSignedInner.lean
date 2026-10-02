import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.Module.BigOperators

/-!
# A `{-1,0,1}`-signed regrouping of generators is an inner-approximation

`[1, Thm. 3]`: if every row of `T` has exactly one nonzero entry, itself `±1`
(so `∑ⱼ |Tᵢⱼ| = 1` for every row `i`), then `Zr = {GT, c}` is an
inner-approximation of `Z = {G, c}` — a signed regrouping of `Z`'s generators
into fewer of `Zr`'s.

The paper reaches this through the Sadraddini–Tedrake zonotope-containment
condition (its own `Lemma 3`, with `Γ := T`, `β := 0`) — restated on the page
but not drawn on here, since it is an external citation this tree does not
otherwise carry. This file proves the inclusion directly instead, by the same
triangle-inequality argument `Lemma 3`'s own proof would give at that choice
of `Γ`, `β`.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: `Zr = {GT, c}` is an inner-approximation of `Z = {G, c}`
whenever `T` has entries in `{-1, 0, 1}` with each row summing to `1` in
absolute value. -/
theorem Zonotope.reduceSigned_inner {nr : ℕ} (Z : Zonotope α) (T : Fin Z.h → Fin nr → ℝ)
    (_hT1 : ∀ i j, T i j = -1 ∨ T i j = 0 ∨ T i j = 1) (hT2 : ∀ i, ∑ j, |T i j| = 1) :
    (⟨nr, Z.c, fun j => ∑ i, T i j • Z.G i⟩ : Zonotope α).construct
      ⊆ Z.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, rfl⟩
  refine ⟨fun i => ∑ j, T i j * β j, fun i => ?_, ?_⟩
  · calc |∑ j, T i j * β j| ≤ ∑ j, |T i j * β j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |T i j| * |β j| := by simp [abs_mul]
      _ ≤ ∑ j, |T i j| * 1 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg _)
      _ = ∑ j, |T i j| := by simp
      _ = 1 := hT2 i
  · show Z.c + ∑ j, β j • (∑ i, T i j • Z.G i)
        = Z.c + ∑ i, (∑ j, T i j * β j) • Z.G i
    congr 1
    rw [Finset.sum_congr rfl (fun j _ => Finset.smul_sum), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [smul_smul, mul_comm (β _) (T i _)]
    rw [Finset.sum_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
