module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
public import CORALean.ContSet.ConZonotope.Real.Operations.Tighten

@[expose] public section

/-!
# `ConZonotope.tightenER`'s box after one pass is `tighten`'s

The `E` half of [1, Alg. 1 (iteration)] ([2, Alg. 1]), run once, is the box `tighten` already
computes: `R` is carried beside `E` and never read by it. So everything proved of `tighten` is a
fact about `tightenER`'s `E` at `k = 0`.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset

## Hypotheses
* none

## Conclusion
* the box after one pass is the tightened box

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A fold whose first component evolves on its own is the fold of that component. -/
theorem ConZonotope.aux_foldl_fst {α β : Type} (n : ℕ) (f : α × β → Fin n → α × β)
    (g : α → Fin n → α) (hfg : ∀ s i, (f s i).1 = g s.1 i) (x : α × β) : -- --- CONCL ---
    (Fin.foldl n f x).1 = Fin.foldl n g x.1 := by -- --- PROOF ---
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last, hfg,
        ih (fun s i => f s i.castSucc) (fun s i => g s i.castSucc) (fun s i => hfg s _)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (iteration)]: the `E` that `tightenER` returns after one pass is `tighten`'s. -/
theorem ConZonotope.tightenER_zero_fst {nc ng : ℕ} (A : Mat ℝ nc ng)
    (b : Vec ℝ nc) : -- --- CONCL ---
    (ConZonotope.tightenER A b 0).1 = ConZonotope.tighten A b := by -- --- PROOF ---
  unfold ConZonotope.tightenER ConZonotope.tighten ConZonotope.tightenPassER
  refine ConZonotope.aux_foldl_fst nc _ _ (fun S i => ?_) _
  -- within a row, the coefficient step's `E` is `tightenCoeff`'s
  unfold ConZonotope.tightenRow
  refine ConZonotope.aux_foldl_fst ng _ _ (fun S' j => ?_) _
  unfold ConZonotope.tightenCoeffER ConZonotope.tightenCoeff
  split_ifs <;> rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
