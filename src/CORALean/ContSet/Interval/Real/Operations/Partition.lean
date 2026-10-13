import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.partition`

CORA's `@interval/partition(I, splits)`: cut every coordinate into `splits` equal pieces and
return the `splits ^ n` sub-boxes, indexed by which piece each coordinate took. CORA returns them as
a cell array; here the index tuple `Fin n → Fin splits` is the position in it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sub-box whose coordinate `i` is the `ind i`-th of `splits` equal pieces of
`[inf i, sup i]`. -/
noncomputable def Interval.partition (I : Interval (Vec ℝ n)) (splits : ℕ)
    (ind : Fin n → Fin splits) : Interval (Vec ℝ n) where
  inf := fun i => I.inf i + (ind i : ℝ) * ((I.sup i - I.inf i) / splits)
  sup := fun i => I.inf i + ((ind i : ℝ) + 1) * ((I.sup i - I.inf i) / splits)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
