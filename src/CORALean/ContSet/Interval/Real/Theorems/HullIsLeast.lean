module

public import CORALean.ContSet.Interval.Real.Definitions.Hull
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# The interval hull is the smallest box

[1, Def. 2]: for a nonempty bounded `S`, `Box(S)` contains `S` and lies in every interval vector
that contains `S`. Each coordinate of `S` is bounded through the sup norm, so its `sSup` and
`sInf` are its least upper and greatest lower bound.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a bounded set has bounded coordinates
theorem Interval.aux_hull_bdd (S : Set (Vec ℝ n)) (hb : Bornology.IsBounded S) (i : Fin n) :
    BddAbove ((fun x : Vec ℝ n => x i) '' S) ∧
      BddBelow ((fun x : Vec ℝ n => x i) '' S) := by -- --- PROOF ---
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have h : ∀ x ∈ S, |x i| ≤ R := fun x hx => by
    exact ((Real.norm_eq_abs (x i)) ▸ norm_le_pi_norm x i).trans
      (mem_closedBall_zero_iff.mp (hR hx))
  exact ⟨⟨R, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (h x hx)).2⟩,
    ⟨-R, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (h x hx)).1⟩⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.hull_isLeast (S : Set (Vec ℝ n)) (hne : S.Nonempty)
    (hb : Bornology.IsBounded S) :
    S ⊆ (Interval.hull S).construct ∧
      ∀ I : Interval (Vec ℝ n), S ⊆ I.construct →
        (Interval.hull S).construct ⊆ I.construct := by -- --- PROOF ---
  have hbdd := Interval.aux_hull_bdd S hb
  refine ⟨fun x hx i => ?_, fun I hI x hx i => ?_⟩
  · -- every point lies between the coordinate's infimum and supremum
    exact ⟨csInf_le (hbdd i).2 ⟨x, hx, rfl⟩, le_csSup (hbdd i).1 ⟨x, hx, rfl⟩⟩
  · -- `I`'s bounds bound the coordinate, so the hull's lie inside them
    have hne' : ((fun x : Vec ℝ n => x i) '' S).Nonempty := hne.image _
    have hlo : Entrywise.entry I.inf i ≤ sInf ((fun x : Vec ℝ n => x i) '' S) :=
      le_csInf hne' (by rintro _ ⟨y, hy, rfl⟩; exact (hI hy i).1)
    have hhi : sSup ((fun x : Vec ℝ n => x i) '' S) ≤ Entrywise.entry I.sup i :=
      csSup_le hne' (by rintro _ ⟨y, hy, rfl⟩; exact (hI hy i).2)
    exact ⟨hlo.trans (hx i).1, (hx i).2.trans hhi⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
