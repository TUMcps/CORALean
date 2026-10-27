module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox
public import CORALean.Global.EuclideanHausdorffDist
public import CORALean.Global.Err

@[expose] public section

/-!
# [1, Prop. 4] at an order rather than at a partition

`hausdorffDist₂_reduceBy_le` states eq. (29) at a `Split` and reads it as `err` of the
dropped generators; `reduce` and the tuning sweeps around it are stated at an *order*, and
the number they carry is `reduceBoxError`. This is the same bound in those terms:
`d_H(Z, reduce(Z,ρ)) ≤ Δε^r_k(ρ)`, at every order, the no-op branch included.

The proof is the one eq. (29) asks for with the attainment step already spent: `reduce_outer`
gives one direction for nothing, `reduce_subset_add_box` turns the other into a point of the
substituted box, and `absBound` is exactly what `reduceBoxError` takes the `‖·‖₂` of.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reduction moves the zonotope by at most the box error

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4], eq. (29) at an order: one reduction to order `ρ` moves a zonotope by at
most `Δε^r_k(ρ)`, the `err` of the box it absorbs the dropped generators into. -/
theorem Zonotope.hausdorffDist₂_reduce_le (Z : Zonotope (Vec ℝ n)) (o : ℕ) : -- --- CONCL ---
    hausdorffDist₂ Z.construct (Z.reduce o).construct ≤ Z.reduceBoxError o := by -- --- PROOF ---
  refine hausdorffDist₂_le_of_mem_dist (norm₂_nonneg _) (fun x hx => ?_) (fun y hy => ?_)
  · exact ⟨x, Z.reduce_outer o hx, by rw [sub_self, norm₂_zero]; exact norm₂_nonneg _⟩
  -- the other way the reduction only added the box, and `absBound` is what bounds that
  · obtain ⟨z, hz, b, hb, rfl⟩ := Set.mem_add.mp (Z.reduce_subset_add_box o hy)
    refine ⟨z, hz, ?_⟩
    rw [show z + b - z = b by abel]
    obtain ⟨β, hβ, hbi⟩ := Zonotope.mem_construct_iff.mp hb
    simp only [Zonotope.reduceBoxError, norm₂]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
    calc b j ^ 2 = |b j| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (Zonotope.abs_le_absBound hβ hbi j) 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
