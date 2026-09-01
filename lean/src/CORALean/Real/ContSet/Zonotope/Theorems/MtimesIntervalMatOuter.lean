import CORALean.Real.ContSet.Zonotope.Operations.MtimesIntervalMat
import CORALean.Real.ContSet.Zonotope.Theorems.Coefficient

/-!
# Multiplying by an interval matrix over-approximates every matrix in it

Outer and never exact: the boxed generators are one per coordinate, so what the
radius does to different coordinates is allowed to vary independently, which the
matrices denoted do not.

The centre part is `mtimes` exactly; the whole content is that the leftover
`(A - centre) x` fits inside the diagonal block, which it does because a
coordinate of a zonotope never exceeds `absBound`.

Nonnegativity of the radius is read off the witness rather than assumed: an
`IntervalMat` with crossed bounds denotes nothing, and then there is nothing to
prove.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {m n : ℕ}

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_mtimesIntervalMat {IM : IntervalMat m n} {Z : Zonotope n}
    (f : Fin (Z.h + m) → ℝ) :
    ∑ j : Fin (Zonotope.mtimesIntervalMat IM Z).h, f j
      = ∑ j, f (Fin.castAdd m j) + ∑ j, f (Fin.natAdd Z.h j) :=
  Fin.sum_univ_add f

/-- A coordinate of a zonotope never leaves `absBound`. -/
theorem Zonotope.aux_abs_le_absBound {Z : Zonotope n} {x : Vec ℝ n} {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (hx : ∀ i, x i = Z.c i + ∑ j, Z.G i j * β j) (j : Fin n) :
    |x j| ≤ Z.absBound j := by
  rw [hx j, Zonotope.absBound]
  refine (abs_add_le _ _).trans ?_
  gcongr
  calc |∑ l, Z.G j l * β l|
      ≤ ∑ l, |Z.G j l * β l|   := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, |Z.G j l| * |β l| := by simp_rw [abs_mul]
    _ ≤ ∑ l, |Z.G j l|         := Finset.sum_le_sum fun l _ => by
        simpa using mul_le_mul_of_nonneg_left (hβ l) (abs_nonneg (Z.G j l))

set_option maxHeartbeats 40000 in
theorem Zonotope.mtimesIntervalMat_outer (IM : IntervalMat m n) (Z : Zonotope n) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' Z.construct)
      ⊆ (Zonotope.mtimesIntervalMat IM Z).construct := by
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, ⟨β, hβ, hx⟩, rfl⟩ := hy
  have hrad : ∀ i j, 0 ≤ IM.radius i j :=
    fun i j => (abs_nonneg _).trans (IM.abs_sub_center_le hA i j)
  have hxb := Zonotope.aux_abs_le_absBound hβ hx
  -- what the radius is allowed to add to coordinate `i`
  set err : Fin m → ℝ := fun i => ∑ j, (A i j - IM.center i j) * x j with herr
  have herrb : ∀ i, |err i| ≤ Zonotope.radiusReach IM Z i := by
    intro i
    calc |err i|
        ≤ ∑ j, |(A i j - IM.center i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j - IM.center i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, IM.radius i j * Z.absBound j := Finset.sum_le_sum fun j _ =>
          mul_le_mul (IM.abs_sub_center_le hA i j) (hxb j) (abs_nonneg _) (hrad i j)
      _ = Zonotope.radiusReach IM Z i := rfl
  have hreachnn : ∀ i, 0 ≤ Zonotope.radiusReach IM Z i :=
    fun i => (abs_nonneg _).trans (herrb i)
  refine ⟨Fin.append β (fun i => Zonotope.coefficient (Zonotope.radiusReach IM Z i) (err i)),
    ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ l
    · simp only [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (hreachnn i) (herrb i)
  · rw [Zonotope.aux_sum_univ_mtimesIntervalMat]
    simp only [Zonotope.mtimesIntervalMat, Fin.append_left, Fin.append_right]
    rw [Zonotope.sum_diagonal_mul, Zonotope.mul_coefficient (herrb i)]
    -- centre acts exactly, and the leftover is `err`
    have hcentre : ∑ l, (IM.center * Z.G) i l * β l
        = ∑ j, IM.center i j * (∑ l, Z.G j l * β l) := by
      simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    rw [hcentre]
    have hsplit : (A *ᵥ x) i = (∑ j, IM.center i j * x j) + err i := by
      simp only [herr, Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcx : ∑ j, IM.center i j * x j
        = (IM.center *ᵥ Z.c) i + ∑ j, IM.center i j * (∑ l, Z.G j l * β l) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hx j]; ring
    rw [hsplit, hcx]
    ring

end CORALean.Real
