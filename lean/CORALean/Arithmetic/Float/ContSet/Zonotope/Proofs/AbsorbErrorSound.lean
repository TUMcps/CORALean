import CORALean.Arithmetic.Float.ContSet.Zonotope.API
import CORALean.Arithmetic.Real.ContSet.Zonotope.Proofs.Coefficient

/-!
# `absorbError` keeps the set it had

Over ℝ this is an identity — a box is a zonotope about its own midpoint, so
trading it for `n` generators moves nothing. What makes it an inclusion here is
that the shifted centre has to be stored as a float and the midpoint need not be
one, which is why the box does not become `[0, 0]`.

The witness is `Fin.append β γ`: the old coefficients, then one per coordinate
placing that coordinate's error inside its new generator. `coefficient` supplies
it, and the radius rounds up so it always fits.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic CORALean.Arithmetic.Real.Zonotope.Proofs

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

/-- The new generators reach every point the box did. -/
theorem abs_sub_mid_le_errorRadius (Z : Zonotope F n h) {e : Vec ℝ n}
    (he : e ∈ Z.E.construct) (i : Fin n) :
    |e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2| ≤ toReal (Z.errorRadius i) := by
  have hwidth := sub_le_subUp (Z.E.sup i) (Z.E.inf i)
  -- ascribed, so `toRealVec _ i` is unfolded to the atom linarith shares with hwidth
  have hlo : toReal (Z.E.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (Z.E.sup i) := (he i).2
  simp only [Zonotope.errorRadius, toReal_half]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The stored centre brackets the exact shifted one, which is what the leftover
box is built from. -/
theorem shift_brackets_mid (Z : Zonotope F n h) (i : Fin n) :
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

theorem toReal_diagonalBlock (v : Vec F n) (i l : Fin n) :
    toReal (diagonalBlock v i l) = Matrix.diagonal (toRealVec v) i l := by
  by_cases hil : i = l
  · rw [diagonalBlock, if_pos hil, hil, Matrix.diagonal_apply_eq]
    rfl
  · rw [diagonalBlock, if_neg hil, Matrix.diagonal_apply_ne _ hil, toReal_zero]

theorem absorbError_sound (Z : Zonotope F n h) :
    Z.construct ⊆ Z.absorbError.construct := by
  rintro _ ⟨z, ⟨β, hβ, hz⟩, e, he, rfl⟩
  refine ⟨fun i => toReal (Z.absorbError.c i)
            + ∑ j, toReal (Z.absorbError.G i j)
                * Fin.append β (fun l => coefficient (toReal (Z.errorRadius l))
                    (e l - (toReal (Z.E.inf l) + toReal (Z.E.sup l)) / 2)) j,
          ⟨_, ?_, fun _ => rfl⟩,
          fun i => toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ l
    · simpa using abs_coefficient_le_one
        ((abs_nonneg _).trans (abs_sub_mid_le_errorRadius Z he l))
        (abs_sub_mid_le_errorRadius Z he l)
  · exact InflatedContSet.sub_mem_residual (shift_brackets_mid Z)
  · funext i
    simp only [Zonotope.absorbError, Zonotope.toExact, toRealMat, toRealVec, Pi.add_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, toReal_diagonalBlock, hz i]
    rw [sum_diagonal_mul]
    simp only [toRealVec]
    rw [mul_coefficient (abs_sub_mid_le_errorRadius Z he i)]
    ring

end CORALean.Arithmetic.Float.Zonotope.Proofs
