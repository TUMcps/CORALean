import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

/-!
# Multiplying a polynomial zonotope by an interval matrix over-approximates

Outer and never exact: the boxed generators are one per coordinate, so what the
radius does to different coordinates is allowed to vary independently, which
the matrices denoted do not.

The centre part is `mtimes` exactly on every block; the leftover `(A - centre)
x` fits in the fresh independent generators because `x`, read through the
enclosing zonotope's coefficients (the dependent monomials appended to the
independent ones), never exceeds `pZ.zonotope.absBound`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at this operation's independent generator count, stated
through the projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_mtimesIntervalMat {IM : Interval (Mat ℝ m n)}
    {pZ : PolyZonotope (Vec ℝ n)} (f : Fin (pZ.q + m) → ℝ) :
    ∑ j : Fin (PolyZonotope.mtimesIntervalMat IM pZ).q, f j
      = ∑ j, f (Fin.castAdd m j) + ∑ j, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The dependent block keeps `pZ.h` generators, but the goal still reads the
count through the operation's own projection; `rfl` is what identifies the two,
the same gap `aux_sum_univ_mtimesIntervalMat` closes for the independent one. -/
theorem PolyZonotope.aux_sum_univ_mtimesIntervalMat_dep {IM : Interval (Mat ℝ m n)}
    {pZ : PolyZonotope (Vec ℝ n)} (f : Fin pZ.h → ℝ) :
    ∑ l : Fin (PolyZonotope.mtimesIntervalMat IM pZ).h, f l = ∑ l, f l :=
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

-- the image sits in the centre's polynomial zonotope widened by what the radius can reach
theorem PolyZonotope.mtimesIntervalMat_outer (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' pZ.construct)
      ⊆ (PolyZonotope.mtimesIntervalMat IM pZ).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_construct_iff.mp hxmem
  have hrad : ∀ i j, 0 ≤ IM.radius i j :=
    fun i j => (abs_nonneg _).trans (IM.abs_sub_center_le hA (i, j))
  -- `x` bounded through the enclosing zonotope, which never grows what a point can reach
  obtain ⟨γ, hγ, hxz⟩ := Zonotope.mem_construct_iff.mp (PolyZonotope.zonotope_contains pZ hxmem)
  have hxb := fun j => Zonotope.abs_le_absBound hγ hxz j
  -- what the radius is allowed to add to coordinate `i`
  set err : Fin m → ℝ := fun i => ∑ j, (A i j - IM.center i j) * x j with herr
  have herrb : ∀ i, |err i| ≤ PolyZonotope.radiusReach IM pZ i := by
    intro i
    calc |err i|
        ≤ ∑ j, |(A i j - IM.center i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j - IM.center i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, IM.radius i j * pZ.zonotope.absBound j := Finset.sum_le_sum fun j _ =>
          mul_le_mul (IM.abs_sub_center_le hA (i, j)) (hxb j) (abs_nonneg _) (hrad i j)
      _ = PolyZonotope.radiusReach IM pZ i := rfl
  have hreachnn : ∀ i, 0 ≤ PolyZonotope.radiusReach IM pZ i :=
    fun i => (abs_nonneg _).trans (herrb i)
  -- the witness: the old factors and coefficients, plus one per coordinate scaled to that reach
  refine PolyZonotope.mem_construct_iff.mpr
    ⟨a, Fin.append β (fun i => Zonotope.coefficient (PolyZonotope.radiusReach IM pZ i) (err i)),
    ha, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ l
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hreachnn i) (herrb i)
  · rw [PolyZonotope.aux_sum_univ_mtimesIntervalMat,
      PolyZonotope.aux_sum_univ_mtimesIntervalMat_dep]
    simp only [PolyZonotope.mtimesIntervalMat, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (herrb i)]
    -- centre acts exactly on the dependent block and on the old independent one
    have hcentreG : ∑ l, (IM.center *ᵥ pZ.G l) i * PolyZonotope.monomial pZ.E a l
        = ∑ j, IM.center i j * (∑ l, pZ.G l j * PolyZonotope.monomial pZ.E a l) := by
      simp_rw [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    have hcentreGI : ∑ k, (IM.center *ᵥ pZ.GI k) i * β k
        = ∑ j, IM.center i j * (∑ k, pZ.GI k j * β k) := by
      simp_rw [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    rw [hcentreG, hcentreGI]
    -- what remains is `x`'s own decomposition, weighted by the centre and split off `err`
    have hsplit : (A *ᵥ x) i = (∑ j, IM.center i j * x j) + err i := by
      simp only [herr, Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcx : ∑ j, IM.center i j * x j
        = (IM.center *ᵥ pZ.c) i
          + ∑ j, IM.center i j * (∑ l, pZ.G l j * PolyZonotope.monomial pZ.E a l)
          + ∑ j, IM.center i j * (∑ k, pZ.GI k j * β k) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hx j]; ring
    rw [hsplit, hcx]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
