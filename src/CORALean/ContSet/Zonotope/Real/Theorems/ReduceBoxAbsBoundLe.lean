import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

/-!
# `reduceBox` never reaches further than the zonotope it was cut from

A crude but unconditional bound, at every order: the box only ever sums a
subset of the dropped generators' entries at a coordinate, no matter how the
order was chosen, so it never exceeds the same coordinate's `absBound` on the
whole zonotope. Nothing here uses which generators `girardSplit` actually
keeps — the bound holds however the partition is chosen, which is what lets a
caller use `Z`'s own outer ball for the box term without knowing the order in
advance.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The box's own `absBound`, read off its diagonal generators at a
coordinate: the dropped rows' `1`-norm there, and nothing from the centre. -/
theorem aux_reduceByBox_absBound {n q r : ℕ} (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (j : Fin n) :
    (Z.reduceByBox part).absBound j = ∑ l, |Z.G (part.right l) j| := by -- --- PROOF ---
  show |(0 : Vec ℝ n) j| + ∑ l : Fin n,
      |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) l j| = ∑ l, |Z.G (part.right l) j|
  rw [Pi.zero_apply, abs_zero, zero_add]
  have hsingle : (∑ l, |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) l j|)
      = |Matrix.diagonal (fun i => ∑ l, |Z.G (part.right l) i|) j j| :=
    Finset.sum_eq_single j (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb, abs_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
  rw [hsingle, Matrix.diagonal_apply_eq,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reduceBox`'s own `absBound` never exceeds the source zonotope's: a
dropped generator is one of `Z`'s own, and the origin at an order already met
is no further than `Z`'s own centre, `absBound` being non-negative. -/
theorem Zonotope.reduceBox_absBound_le (Z : Zonotope (Vec ℝ n)) (o : ℕ) (j : Fin n) :
    (Z.reduceBox o).absBound j ≤ Z.absBound j := by -- --- PROOF ---
  unfold Zonotope.reduceBox
  split_ifs with hlt
  · rw [aux_reduceByBox_absBound]
    calc ∑ l, |Z.G ((Z.girardSplit o hlt).right l) j|
        ≤ ∑ l, |Z.G ((Z.girardSplit o hlt).left l) j|
            + ∑ l, |Z.G ((Z.girardSplit o hlt).right l) j| :=
          le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = ∑ l, |Z.G l j| := ((Z.girardSplit o hlt).sum_split₂ fun l => |Z.G l j|).symm
      _ ≤ Z.absBound j := by
          rw [Zonotope.absBound]; exact le_add_of_nonneg_left (abs_nonneg _)
  · rw [Zonotope.absBound]
    simp only [Zonotope.ofPoint, Pi.zero_apply, abs_zero, zero_add, Finset.univ_eq_empty,
      Finset.sum_empty]
    rw [Zonotope.absBound]; positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
