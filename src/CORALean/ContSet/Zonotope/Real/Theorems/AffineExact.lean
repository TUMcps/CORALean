module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# An affine map of a zonotope is exact

[1, Sec. IV-A (Aff)]: the zonotope domain supports `Aff`, `x ↦ W x + b`, and loses nothing.
`mtimes` then `plus` with the point `b`: the linear part by `mtimes_exact`, the translation by
`plus_exact` against a zonotope with no generators.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the affine image of `Z` equals the zonotope of `affine`

## References

* [1] [T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP),
      2018.](../../../../../../references/2018/gehr-sp-ai2.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.affine_exact (W : Mat ℝ m n) (b : Vec ℝ m)
    (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (fun x => W *ᵥ x + b) '' Z.construct
      = ((Zonotope.mtimes W Z).plus (Zonotope.ofPoint b)).construct := by -- --- PROOF ---
  rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
  -- the point zonotope is `{b}`, so the sum is a translate
  have hpt : (Zonotope.ofPoint b).construct = {b} :=
    Set.ext fun x => Zonotope.mem_ofPoint_iff b x
  rw [hpt, Set.add_singleton, Set.image_image]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
