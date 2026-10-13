module

public import CORALean.ContSet.Interval.Real.Operations.Enlarge
public import CORALean.ContSet.Interval.Real.Theorems.IntervalMatrixEq
public import CORALean.ContSet.Interval.Real.Theorems.MemOfCenterRadius
public import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
public import CORALean.ContSet.Interval.Real.Theorems.MemCenter

@[expose] public section

/-!
# `Interval.enlarge` is exactly the box scaled about its centre

For a nonnegative factor `f` and a nonempty box, `[c - f·r, c + f·r]` is the image of the box under
`x ↦ c + f·(x - c)`, the scaling about the centre `c` (`enlarge_exact`). A factor of zero collapses
the box to its centre, which a nonempty box contains. Nonemptiness is needed: the image of an
empty box is empty, while its enlargement may not be (a crossed box has a negative half-width,
and a negative half-width times a factor is again negative, but a factor of zero gives the
point).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [inst : Entrywise α ι]

include inst


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.enlarge_exact {I : Interval α} (hI : I.IsNonempty (ι := ι)) {f : ℝ}
    (hf : 0 ≤ f) :
    (I.enlarge f).construct =
      (fun x => I.center + f • (x - I.center)) '' I.construct := by -- --- PROOF ---
  -- a point of the box is a point of `ofCenterRadius center radius`, which is the box itself
  have hbox : ∀ y, y ∈ (Interval.ofCenterRadius I.center I.radius).construct → y ∈ I.construct :=
    fun y hy => by
      have h := Interval.intervalMatrix_eq I
      unfold Interval.intervalMatrix at h
      rwa [h] at hy
  ext z
  constructor
  · intro hz
    -- the target is within `f · radius` of the centre
    have hz' := (Interval.mem_ofCenterRadius _ _ z).1 hz
    simp only [entry_smul] at hz'
    rcases hf.eq_or_lt with hf0 | hfpos
    · -- a factor of zero: the box collapses to its centre
      refine ⟨I.center, Interval.mem_center I hI, ?_⟩
      refine Entrywise.ext fun i => ?_
      have h := hz' i
      rw [← hf0] at h
      simp only [zero_mul, abs_nonpos_iff, sub_eq_zero] at h
      simp only [entry_add, entry_smul, ← hf0, zero_mul, add_zero, h]
    · -- otherwise scale back by `f⁻¹`
      refine ⟨I.center + f⁻¹ • (z - I.center), ?_, ?_⟩
      · refine hbox _ ((Interval.mem_ofCenterRadius _ _ _).2 fun i => ?_)
        simp only [entry_add, entry_smul, entry_sub, add_sub_cancel_left, abs_mul,
          abs_inv, abs_of_pos hfpos]
        have h := hz' i
        calc f⁻¹ * |entry z i - entry I.center i| ≤ f⁻¹ * (f * entry I.radius i) := by
              gcongr
          _ = entry I.radius i := by field_simp
      · simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hfpos.ne', one_smul]
        abel
  · -- the scaled member stays within `f · radius`
    rintro ⟨x, hx, rfl⟩
    refine (Interval.mem_ofCenterRadius _ _ _).2 fun i => ?_
    have h := Interval.abs_sub_center_le hx i
    simp only [entry_add, entry_smul, entry_sub, add_sub_cancel_left, abs_mul, abs_of_nonneg hf]
    exact mul_le_mul_of_nonneg_left h hf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
