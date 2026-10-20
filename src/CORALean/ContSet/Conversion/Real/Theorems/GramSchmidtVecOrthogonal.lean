module

public import CORALean.ContSet.Conversion.Real.Definitions.GramSchmidt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# CORA's one-column `gramSchmidt(g)` is an orthogonal matrix

For `g ≠ 0` the completed columns `g, e_{j}` (`j` running over every index but the pivot) are
independent: the pivot coordinate of a combination reads the coefficient of `g` times
`g_pivot ≠ 0`, and every other coordinate reads its own unit column's coefficient. Mathlib's
`gramSchmidtNormed_orthonormal` then makes the result orthonormal, which over `Vec ℝ (m + 1)` is
`Qᵀ Q = 1`. A square matrix with a left inverse has it as a right inverse too, so `Q Qᵀ = 1`
follows (`Matrix.mul_eq_one_comm`), and with it that every vector is the sum of its components
along the columns.

## Inputs
* `g` – vector

## Hypotheses
* `hg` – vector nonzero

## Conclusion
* transpose times matrix is the identity
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonzero vector is nonzero at its pivot, the first largest `|gᵢ|`. -/
theorem aux_gramSchmidtPivot_ne_zero {g : Vec ℝ (m + 1)} (hg : g ≠ 0) : -- --- CONCL ---
    g (gramSchmidtPivot g) ≠ 0 := by -- --- PROOF ---
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  -- the pivot is the `argmax` of `|g ·|` over a nonempty list
  obtain ⟨p, hp⟩ : ∃ p, (List.finRange (m + 1)).argmax (fun i => |g i|) = some p := by
    cases h : (List.finRange (m + 1)).argmax (fun i => |g i|) with
    | none => exact absurd (List.argmax_eq_none.mp h) (List.ne_nil_of_mem (List.mem_finRange 0))
    | some p => exact ⟨p, rfl⟩
  have hpiv : gramSchmidtPivot g = p := by
    simp only [gramSchmidtPivot, hp, Option.getD_some]
  have hle : |g i| ≤ |g p| := List.le_of_mem_argmax (f := fun i => |g i|) (List.mem_finRange i) hp
  rw [hpiv]
  intro h0
  rw [h0, abs_zero] at hle
  exact hi (abs_nonpos_iff.mp hle)

/-- The completed columns are independent once `g` is nonzero at the dropped index `p`. -/
theorem aux_gramSchmidtVec_cols_independent {g : Vec ℝ (m + 1)} {p : Fin (m + 1)}
    (hgp : g p ≠ 0) : -- --- CONCL ---
    LinearIndependent ℝ (Matrix.of fun i j => Fin.cases (motive := fun _ => ℝ)
      (g i) (fun l => (Pi.single (p.succAbove l) 1 : Vec ℝ (m + 1)) i) j)ᵀ := by -- --- PROOF ---
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- each coordinate of the combination, with the first column split off
  have hcoord : ∀ i, c 0 * g i + ∑ l : Fin m,
      c l.succ * (Pi.single (p.succAbove l) 1 : Vec ℝ (m + 1)) i = 0 := by
    intro i
    have := congrFun hc i
    simpa [Fin.sum_univ_succ, Finset.sum_apply, smul_eq_mul, transpose_apply] using this
  -- the coordinate `p` sees `g` alone, since no unit column sits there
  have h0 : c 0 = 0 := by
    have hpiv := hcoord p
    have hsum : ∑ l : Fin m, c l.succ * (Pi.single (p.succAbove l) 1 : Vec ℝ (m + 1)) p = 0 :=
      Finset.sum_eq_zero fun l _ => by
        rw [Pi.single_apply, if_neg (Fin.succAbove_ne p l).symm, mul_zero]
    rw [hsum, add_zero] at hpiv
    exact (mul_eq_zero.mp hpiv).resolve_right hgp
  intro j
  refine Fin.cases h0 (fun l => ?_) j
  -- the coordinate `p.succAbove l` sees the `l`-th unit column alone
  have hl := hcoord (p.succAbove l)
  rw [h0, zero_mul, zero_add] at hl
  rw [Finset.sum_eq_single l] at hl
  · simpa [Pi.single_apply] using hl
  · intro l' _ hl'
    rw [Pi.single_apply, if_neg (fun h => hl' (Fin.succAbove_right_injective h).symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `gramSchmidt(g)` is an orthogonal matrix when `g ≠ 0`: `Qᵀ Q = 1`. -/
theorem gramSchmidtVec_transpose_mul_self {g : Vec ℝ (m + 1)} (hg : g ≠ 0) : -- --- CONCL ---
    (gramSchmidtVec g)ᵀ * gramSchmidtVec g = 1 := by -- --- PROOF ---
  -- the completed columns, independent, read into `EuclideanSpace`
  have hcols := aux_gramSchmidtVec_cols_independent (aux_gramSchmidtPivot_ne_zero hg)
  set f : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) := fun j => toEuclidean fun i =>
    Fin.cases (motive := fun _ => ℝ) (g i)
      (fun l => (Pi.single ((gramSchmidtPivot g).succAbove l) 1 : Vec ℝ (m + 1)) i) j
  have hind : LinearIndependent ℝ f :=
    hcols.map' toEuclidean.toLinearEquiv.toLinearMap toEuclidean.toLinearEquiv.ker
  have hon := orthonormal_iff_ite.mp (InnerProductSpace.gramSchmidtNormed_orthonormal hind)
  ext i j
  -- an entry of `Qᵀ Q` is the inner product of two columns
  have hentry : ((gramSchmidtVec g)ᵀ * gramSchmidtVec g) i j
      = inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ f i)
          (InnerProductSpace.gramSchmidtNormed ℝ f j) := by
    rw [mul_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [transpose_apply, gramSchmidtVec, gramSchmidt, f, Matrix.of_apply,
      RCLike.inner_apply, conj_trivial]
    ring
  rw [hentry, hon i j, one_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
