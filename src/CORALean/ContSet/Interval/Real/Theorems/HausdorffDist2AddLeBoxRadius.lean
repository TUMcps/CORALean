import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.EuclideanHausdorffDist

/-!
# `Prop. 1`: a Minkowski summand's box bounds how far the sum moves

[1, Prop. 1]: `d_H(S=, S= ⊕ S+) ≤ err(S+) := r(box(S+))` when `0 ∈ S+`, `r(·)`
being the radius of the smallest hypersphere at the origin enclosing its
argument — Euclidean, stated here at `hausdorffDist₂`, the norm [1] writes.

`box(S+)` is any `Interval (Vec ℝ n)` containing `S+`, not a canonical
tightest one: [1]'s own proof only uses `S+ ⊆ box(S+)`, so a looser box gives
a true, looser bound, the same leniency every `_outer` result in this tree
already carries. `r` of a box is closed form — the farthest corner from the
origin, per coordinate whichever endpoint has the larger magnitude — rather
than a fresh `sSup`, since a box's own shape already picks it out.

No compactness or nonemptiness hypothesis: `hausdorffDist₂_le_of_mem_dist`
bounds the distance from above regardless, `0 ∈ S+` alone supplying the first
witness and `hB` the second.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point between two endpoints never exceeds the max of their magnitudes. -/
theorem aux_boxRadius_abs_le {lo x hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) : |x| ≤ max |lo| |hi| :=
  abs_le.mpr ⟨by linarith [neg_abs_le lo, neg_le_neg (le_max_left |lo| |hi|)],
    h2.trans ((le_abs_self hi).trans (le_max_right _ _))⟩

/-- Squaring is monotone on magnitudes, so a coordinatewise bound on magnitudes
is a bound on the Euclidean norm. -/
theorem aux_boxRadius_norm₂_le_of_abs_le {x y : Vec ℝ n} (h : ∀ i, |x i| ≤ |y i|) :
    ‖x‖₂ ≤ ‖y‖₂ := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hi := mul_self_le_mul_self (abs_nonneg (x i)) (h i)
  rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at hi

/-- Every member of a box is within its farthest corner's length of the
origin. -/
theorem aux_boxRadius_norm₂_le_of_mem {B : Interval (Vec ℝ n)} {p : Vec ℝ n}
    (hp : p ∈ B.construct) : ‖p‖₂ ≤ ‖fun i => max |B.inf i| |B.sup i|‖₂ := by
  refine aux_boxRadius_norm₂_le_of_abs_le fun i => ?_
  have h := hp i
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg (B.inf i)))]
  exact aux_boxRadius_abs_le h.1 h.2


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: the sum `S ⊕ S+` never moves past `S` by more than `S+`'s box
reaches from the origin, whenever `0 ∈ S+`. -/
theorem hausdorffDist₂_add_le_box_radius {S SPlus : Set (Vec ℝ n)}
    (h0 : (0 : Vec ℝ n) ∈ SPlus) (B : Interval (Vec ℝ n)) (hB : SPlus ⊆ B.construct) :
    hausdorffDist₂ S (S + SPlus) ≤ ‖fun i => max |B.inf i| |B.sup i|‖₂ := by -- --- PROOF ---
  refine hausdorffDist₂_le_of_mem_dist (norm₂_nonneg _) (fun x hx => ⟨x, ?_, ?_⟩) ?_
  · have := Set.add_mem_add hx h0
    rwa [add_zero] at this
  · rw [sub_self, norm₂_zero]; exact norm₂_nonneg _
  -- the other direction: a point of the sum is its own summand plus what `S+` adds
  · rintro y hy
    obtain ⟨s, hs, p, hp, rfl⟩ := Set.mem_add.mp hy
    refine ⟨s, hs, ?_⟩
    rw [add_sub_cancel_left]
    exact aux_boxRadius_norm₂_le_of_mem (hB hp)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
