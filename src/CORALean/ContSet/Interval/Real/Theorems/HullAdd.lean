import CORALean.ContSet.Interval.Real.Definitions.Hull
import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Ring.Lemmas
import CORALean.ContSet.Interval.Real.Operations.Plus
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The interval hull of a Minkowski sum

[1, Property 2]: `Box(S₁ ⊕ S₂) = Box(S₁) ⊕ Box(S₂)`, here for two nonempty bounded sets, from
which the `m`-fold sum follows by induction; [2, Eq. 3] prints it for every pair of sets. A
coordinate of the sum ranges over the sum of the coordinate ranges, whose supremum is the sum of
the suprema (`csSup_add`).

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
* [2] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a bounded set has bounded coordinates
theorem Interval.aux_hullAdd_bdd (S : Set (Vec ℝ n)) (hb : Bornology.IsBounded S) (i : Fin n) :
    BddAbove ((fun x : Vec ℝ n => x i) '' S) ∧
      BddBelow ((fun x : Vec ℝ n => x i) '' S) := by -- --- PROOF ---
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have h : ∀ x ∈ S, |x i| ≤ R := fun x hx =>
    ((Real.norm_eq_abs (x i)) ▸ norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.mp (hR hx))
  exact ⟨⟨R, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (h x hx)).2⟩,
    ⟨-R, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (h x hx)).1⟩⟩

-- a coordinate of a Minkowski sum ranges over the sum of the coordinate ranges
theorem Interval.aux_image_add (S T : Set (Vec ℝ n)) (i : Fin n) :
    (fun x : Vec ℝ n => x i) '' (S + T) =
      (fun x : Vec ℝ n => x i) '' S + (fun x : Vec ℝ n => x i) '' T := by -- --- PROOF ---
  ext r
  simp only [Set.mem_image, Set.mem_add]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.hull_add (S T : Set (Vec ℝ n)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hbS : Bornology.IsBounded S) (hbT : Bornology.IsBounded T) :
    Interval.hull (S + T) = (Interval.hull S).plus (Interval.hull T) := by -- --- PROOF ---
  -- coordinate by coordinate, `sInf` and `sSup` of a sum of bounded ranges
  have hS' := Interval.aux_hullAdd_bdd S hbS
  have hT' := Interval.aux_hullAdd_bdd T hbT
  simp only [Interval.hull, Interval.plus]
  congr 1 <;> funext i <;> rw [Interval.aux_image_add]
  · exact csInf_add (hS.image _) (hS' i).2 (hT.image _) (hT' i).2
  · exact csSup_add (hS.image _) (hS' i).1 (hT.image _) (hT' i).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
