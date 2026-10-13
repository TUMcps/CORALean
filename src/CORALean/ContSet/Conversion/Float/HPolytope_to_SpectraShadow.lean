import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A polytope as a spectrahedral shadow, over a floating-point scalar

CORA's `@polytope/spectraShadow`: one `1 × 1` block `d_j - C_j x` per row of the stacked
`C = [A; Ae; -Ae]`, `d = [b; be; -be]`, as the diagonal `A₀ = diag(d)`, `Aᵢ = -diag(C(:,i))`.
The equality rows are the slab `be.inf ≤ Ae x ≤ be.sup` the float polytope denotes, so the stacked
right-hand side is `[b; be.sup; -be.inf]`. Every entry is an existing entry, a negation or a
`zero`, `one`: nothing rounds, so the error box is `0`. The shadow contains the polytope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


def HPolytope.spectraShadow (P : HPolytope 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := P.m + (P.me + P.me)
  m := n
  -- `A₀ = diag(d)` with `d = [b; be.sup; -be.inf]`
  A₀ := fun p q => if p = q then
    Fin.append P.b (Fin.append P.be.sup fun r => neg (P.be.inf r)) p else zero
  -- `Aᵢ = diag(-C(:,i))` with `C = [A; Ae; -Ae]`
  A := fun i p q => if p = q then neg (Fin.append (fun r => P.A r i)
    (Fin.append (fun r => P.Ae r i) fun r => neg (P.Ae r i)) p) else zero
  c := fun _ => zero
  G := fun j i => if i = j then one else zero
  E := Interval.point fun _ => zero

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A diagonal inequality read as reals: the diagonal of the slacks. -/
theorem HPolytope.aux_lmi_diag {k : ℕ} (d : Fin k → 𝕋) (C : Fin n → Fin k → 𝕋) (x : Vec ℝ n) :
    (toRealMat (fun p q => if p = q then d p else zero) +
      ∑ i, x i • toRealMat (fun p q => if p = q then neg (C i p) else zero) : Mat ℝ k k)
      = diagonal fun p => toReal (d p) - ∑ i, x i * toReal (C i p) := by -- --- PROOF ---
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [toRealMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, toReal_neg,
      sub_eq_add_neg, Finset.sum_neg_distrib]
  · simp [toRealMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hpq, toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- At a point of the polytope the stored inequality is positive semidefinite. -/
theorem HPolytope.posSemidef_spectraShadow (P : HPolytope 𝕋 (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ P.construct) :
    (toRealMat P.spectraShadow.A₀
      + ∑ i, x i • toRealMat (P.spectraShadow.A i)).PosSemidef := by -- --- PROOF ---
  -- the matrix is the diagonal of the slacks
  have hM := HPolytope.aux_lmi_diag (n := n) (𝕋 := 𝕋)
    (Fin.append P.b (Fin.append P.be.sup fun r => neg (P.be.inf r)))
    (fun i => Fin.append (fun r => P.A r i)
      (Fin.append (fun r => P.Ae r i) fun r => neg (P.Ae r i))) x
  refine Eq.mpr (congrArg Matrix.PosSemidef hM) (posSemidef_diagonal_iff.mpr ?_)
  obtain ⟨hA, hAe⟩ := HPolytope.mem_construct_iff.mp hx
  -- the three row groups
  intro p
  refine Fin.addCases (fun r => ?_) (fun p' => Fin.addCases (fun r => ?_) (fun r => ?_) p') p
  · have := hA r
    simp only [Fin.append_left, mulVec, dotProduct, toRealMat] at this ⊢
    simp only [mul_comm (x _)] at this ⊢
    linarith
  · have := (hAe r).2
    simp only [Fin.append_left, Fin.append_right, mulVec, dotProduct, toRealMat] at this ⊢
    simp only [mul_comm (x _)] at this ⊢
    linarith
  · have := (hAe r).1
    simp only [Fin.append_right, mulVec, dotProduct, toRealMat, toReal_neg] at this ⊢
    simp only [mul_comm (x _), neg_mul, Finset.sum_neg_distrib] at this ⊢
    linarith

theorem HPolytope.spectraShadow_contains (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.construct ⊆ P.spectraShadow.construct := by -- --- PROOF ---
  intro x hx
  -- the error box is the origin, so the nominal part carries the point
  refine ⟨x, SpectraShadow.mem_nominalSet_iff.mpr ⟨x, HPolytope.posSemidef_spectraShadow P hx,
    fun i => ?_⟩, 0, ?_, add_zero x⟩
  · simp [HPolytope.spectraShadow, apply_ite (toReal : 𝕋 → ℝ), toReal_zero, toReal_one,
    Finset.sum_ite_eq]
  · -- the origin is the point `zero`
    have h0 : (0 : Vec ℝ n) = toRealVec (fun _ => (zero : 𝕋)) := funext fun i => toReal_zero.symm
    rw [h0]
    exact Interval.mem_point _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
