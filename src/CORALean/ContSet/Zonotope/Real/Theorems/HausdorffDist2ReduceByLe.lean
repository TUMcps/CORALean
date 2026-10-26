module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByDropped
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.Global.EuclideanHausdorffDist
public import CORALean.Global.Err

@[expose] public section

/-!
# What one order reduction costs, as a Hausdorff distance

[1, Prop. 4]'s eq. (29): reducing a zonotope by a partition moves it by at most
`err(⟨0, G_red⟩_Z)`, the `err` of the dropped generators' own origin-centered zonotope.
`Δε^r_k(ρ_k)` is that number, and the accumulation in eq. (28) is eq. (21)'s generic error
propagation applied to it. `reduceBy_outer` makes one direction free, and `reduceBy_subset_add_box`
turns the other into a bound on a point of the substituted box. What is left is the step the
paper leaves implicit — that `err` of the *dropped generators* already pays for the whole box —
by attainment: coordinate `i`'s extreme `∑_l |G_red(i,l)|` is reached by the point whose
coefficients are the signs of row `i`. Stated at `‖·‖₂` through `hausdorffDist₂` ([1, Def. 5]).

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices

## Hypotheses
* none

## Conclusion
* one reduction moves the zonotope by at most the dropped reach

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Coordinate `i`'s extreme is attained: the point whose coefficients are the
signs of row `i` of the dropped generators reaches `∑_l |G_red(i,l)|` there. -/
private theorem Zonotope.aux_dropped_le_sSup (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (i : Fin n) : -- --- CONCL ---
    ∑ l, |Z.G (part.right l) i|
      ≤ sSup ((fun z : Vec ℝ n => z i) ''
          (Z.reduceByDropped part).construct) := by -- --- PROOF ---
  have hβ : ∀ l : Fin (Z.reduceByDropped part).h,
      |(if 0 ≤ Z.G (part.right l) i then (1:ℝ) else -1)| ≤ 1 := fun l => by
    by_cases h : 0 ≤ Z.G (part.right l) i <;> simp [h]
  -- at coordinate `i` each generator meets its own sign, so the row sums in magnitude
  have hsign : ∀ l : Fin r, Z.G (part.right l) i
      * (if 0 ≤ Z.G (part.right l) i then (1:ℝ) else -1) = |Z.G (part.right l) i| := fun l => by
    by_cases h : 0 ≤ Z.G (part.right l) i
    · rw [if_pos h, abs_of_nonneg h, mul_one]
    · rw [if_neg h, abs_of_neg (not_le.mp h)]; ring
  refine le_csSup (bddAbove_eval_image (Z.reduceByDropped part).isBounded_construct i)
    ⟨fun i' => (Z.reduceByDropped part).c i' + ∑ l, (Z.reduceByDropped part).G l i'
        * (if 0 ≤ Z.G (part.right l) i then (1:ℝ) else -1),
      Zonotope.mem_construct_iff.mpr ⟨_, hβ, fun i' => rfl⟩, ?_⟩
  show (0:ℝ) + ∑ l, Z.G (part.right l) i
      * (if 0 ≤ Z.G (part.right l) i then (1:ℝ) else -1) = ∑ l, |Z.G (part.right l) i|
  rw [zero_add]
  exact Finset.sum_congr rfl fun l _ => hsign l

/-- Everything the substituted box reaches is within `err` of the dropped
generators' own zonotope: each coordinate is under that coordinate's row sum,
which `aux_dropped_le_sSup` puts under the box `err` reads. -/
private theorem Zonotope.aux_norm₂_le_err_reduceByDropped (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) {x : Vec ℝ n}
    (hx : x ∈ (Z.reduceByBox part).construct) : -- --- CONCL ---
    ‖x‖₂ ≤ err (Z.reduceByDropped part).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, hxi⟩ := Zonotope.mem_construct_iff.mp hx
  -- the box couples coordinate `i` to its own coefficient and no other
  have hbox : ∀ i, |x i| ≤ ∑ l, |Z.G (part.right l) i| := by
    intro i
    have hD : (0:ℝ) ≤ ∑ l, |Z.G (part.right l) i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hxi' : x i = (∑ l, |Z.G (part.right l) i|) * γ i := by
      rw [hxi i]
      show (0:ℝ) + ∑ l, Matrix.diagonal (fun i' => ∑ l', |Z.G (part.right l') i'|) l i * γ l = _
      rw [zero_add, Zonotope.sum_diagonal_mul']
    rw [hxi', abs_mul, abs_of_nonneg hD]
    exact mul_le_of_le_one_right hD (hγ i)
  have hkey : ∀ i, |x i|
      ≤ max |sSup ((fun z : Vec ℝ n => z i) '' (Z.reduceByDropped part).construct)|
          |sInf ((fun z : Vec ℝ n => z i) '' (Z.reduceByDropped part).construct)| := fun i =>
    (hbox i).trans (((Z.aux_dropped_le_sSup part i).trans (le_abs_self _)).trans (le_max_left _ _))
  simp only [err, norm₂]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hkey i) 2


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4], eq. (29): one order-reduction step moves a zonotope by at most
`err(⟨0, G_red⟩_Z)`, the dropped generators' own reach. -/
theorem Zonotope.hausdorffDist₂_reduceBy_le (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : -- --- CONCL ---
    hausdorffDist₂ Z.construct (Z.reduceBy part).construct
      ≤ err (Z.reduceByDropped part).construct := by -- --- PROOF ---
  refine hausdorffDist₂_le_of_mem_dist (err_nonneg _) (fun x hx => ?_) (fun y hy => ?_)
  · exact ⟨x, Z.reduceBy_outer part hx, by rw [sub_self, norm₂_zero]; exact err_nonneg _⟩
  -- the other way the reduction only added the box, which the dropped generators pay for
  · obtain ⟨z, hz, b, hb, rfl⟩ := Set.mem_add.mp (Z.reduceBy_subset_add_box part hy)
    refine ⟨z, hz, ?_⟩
    rw [show z + b - z = b by abel]
    exact Z.aux_norm₂_le_err_reduceByDropped part hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
