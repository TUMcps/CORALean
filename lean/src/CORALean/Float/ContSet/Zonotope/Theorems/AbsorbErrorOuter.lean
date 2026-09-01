import CORALean.Float.ContSet.Zonotope.Operations.API
import CORALean.Real.ContSet.Zonotope.API

/-!
# `absorbError` keeps the set it had

Over ℝ an identity — a box is a zonotope about its own midpoint. It is only an
inclusion here because the shifted centre must be stored as a float and the
midpoint need not be one, which is why the box does not become `[0, 0]`.

The witness is `Fin.append β γ`: the old coefficients, then one per coordinate
placing that coordinate's error in its new generator. `coefficient` supplies it,
and the radius rounds up so it always fits.

This is the one operation that spends generators, `h + n`, and spending them is
what the caller asked for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope 𝕋 n) : Z.absorbError.h = Z.h + n := rfl

/-- The new generators reach every point the box did. -/
theorem Zonotope.abs_sub_mid_le_errorRadius (Z : Zonotope 𝕋 n) {e : Vec ℝ n}
    (he : e ∈ Z.E.construct) (i : Fin n) :
    |e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2| ≤ toReal (Z.errorRadius i) := by
  have hwidth := sub_le_subUp (Z.E.sup i) (Z.E.inf i)
  -- ascribed, so `toRealVec _ i` is unfolded to the atom linarith shares with hwidth
  have hlo : toReal (Z.E.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.E.sup i) := (he i).2
  simp only [Zonotope.errorRadius, toReal_half]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The stored centres bracket the exact shifted one, which is what is left. -/
theorem Zonotope.shift_brackets_mid (Z : Zonotope 𝕋 n) (i : Fin n) :
    toReal (Z.shiftDown i) ≤ toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2 ∧
      toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2 ≤ toReal (Z.shiftUp i) := by
  constructor
  · have h1 := addDown_le_add (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))
    have h2 := addDown_le_add (Z.E.inf i) (Z.E.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftDown] using by linarith
  · have h1 := add_le_addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))
    have h2 := add_le_addUp (Z.E.inf i) (Z.E.sup i)
    rw [toReal_half] at h1
    simpa only [Zonotope.shiftUp] using by linarith

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `absorbError`'s generator count. -/
theorem Zonotope.aux_sum_univ_absorbError {Z : Zonotope 𝕋 n} (f : Fin (Z.h + n) → ℝ) :
    ∑ j : Fin Z.absorbError.h, f j
      = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd Z.h j) :=
  Fin.sum_univ_add f

theorem Zonotope.absorbError_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.absorbError.construct := by
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hz'
  refine ⟨fun i => toReal (Z.absorbError.c i)
            + ∑ j, toReal (Z.absorbError.G i j)
                * Fin.append β (fun l => Real.Zonotope.coefficient (toReal (Z.errorRadius l))
                    (e l - (toReal (Z.E.inf l) + toReal (Z.E.sup l)) / 2)) j,
          Zonotope.mem_nominalSet_iff.mpr ⟨_, ?_, fun _ => rfl⟩,
          fun i => toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ l
    · simpa using Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (Zonotope.abs_sub_mid_le_errorRadius Z he l))
        (Zonotope.abs_sub_mid_le_errorRadius Z he l)
  · exact Interval.sub_mem_residual (Zonotope.shift_brackets_mid Z)
  · funext i
    simp only [Pi.add_apply]
    rw [Zonotope.aux_sum_univ_absorbError]
    simp only [Zonotope.absorbError, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock, hz i]
    rw [Real.Zonotope.sum_diagonal_mul]
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (Zonotope.abs_sub_mid_le_errorRadius Z he i)]
    ring

end CORALean.Float
