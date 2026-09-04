import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter

/-!
# Multiplying a constrained zonotope by an interval matrix over-approximates

The zonotope argument unchanged — the centre acts exactly and the leftover
`(A - centre) x` fits in the diagonal block because a coordinate never exceeds
`absBound` — with one step added: the constraints were pulled back along the
projection onto the original coefficients, so the concatenated witness satisfies
them exactly when the original half did, which is `blockLeft_append`.

Outer and never exact, for the zonotope's reason: the boxed generators let
different coordinates use the radius independently, which the matrices denoted
do not.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {m n : ℕ}

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has. -/
theorem ConZonotope.aux_sum_univ_mtimesIntervalMat {IM : Interval (Mat ℝ m n)}
    {C : ConZonotope (Vec ℝ n)} (f : Fin (C.h + m) → ℝ) :
    ∑ j : Fin (ConZonotope.mtimesIntervalMat IM C).h, f j
      = ∑ j, f (Fin.castAdd m j) + ∑ j, f (Fin.natAdd C.h j) :=
  Fin.sum_univ_add f

-- the nested `Finset.sum` rewrites over the appended generator block are what costs here
set_option maxHeartbeats 400000 in
theorem ConZonotope.mtimesIntervalMat_outer (IM : Interval (Mat ℝ m n))
    (C : ConZonotope (Vec ℝ n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' C.construct)
      ⊆ (ConZonotope.mtimesIntervalMat IM C).construct := by
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_construct_iff.mp hxmem
  have hrad : ∀ i j, 0 ≤ IM.radius i j :=
    fun i j => (abs_nonneg _).trans (IM.abs_sub_center_le hA (i, j))
  have hxb := Zonotope.abs_le_absBound (Z := C.zonotope) hβ hx
  -- what the radius is allowed to add to coordinate `i`
  set err : Fin m → ℝ := fun i => ∑ j, (A i j - IM.center i j) * x j with herr
  have herrb : ∀ i, |err i| ≤ Zonotope.radiusReach IM C.zonotope i := by
    intro i
    calc |err i|
        ≤ ∑ j, |(A i j - IM.center i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j - IM.center i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, IM.radius i j * C.zonotope.absBound j := Finset.sum_le_sum fun j _ =>
          mul_le_mul (IM.abs_sub_center_le hA (i, j)) (hxb j) (abs_nonneg _) (hrad i j)
      _ = Zonotope.radiusReach IM C.zonotope i := rfl
  have hreachnn : ∀ i, 0 ≤ Zonotope.radiusReach IM C.zonotope i :=
    fun i => (abs_nonneg _).trans (herrb i)
  -- the witness: the old coefficients, plus one per coordinate scaled to that reach
  refine ConZonotope.mem_construct_iff.mpr
    ⟨Fin.append β fun i => Zonotope.coefficient (Zonotope.radiusReach IM C.zonotope i) (err i),
      ?_, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) fun l => ?_
    · rw [Fin.append_left]; exact hβ l
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hreachnn l) (herrb l)
  · show blockLeft C.h m (Fin.append β _) ∈ C.P.construct
    rw [blockLeft_append]
    exact hP
  · rw [ConZonotope.aux_sum_univ_mtimesIntervalMat]
    simp only [ConZonotope.mtimesIntervalMat, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul', Zonotope.mul_coefficient (herrb i)]
    -- centre acts exactly, and the leftover is `err`
    have hcentre : ∑ l, (IM.center *ᵥ C.G l) i * β l
        = ∑ j, IM.center i j * (∑ l, C.G l j * β l) := by
      simp_rw [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    rw [hcentre]
    have hsplit : (A *ᵥ x) i = (∑ j, IM.center i j * x j) + err i := by
      simp only [herr, Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcx : ∑ j, IM.center i j * x j
        = (IM.center *ᵥ C.c) i + ∑ j, IM.center i j * (∑ l, C.G l j * β l) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hx j]; ring
    rw [hsplit, hcx]
    ring

end CORALean.Real
