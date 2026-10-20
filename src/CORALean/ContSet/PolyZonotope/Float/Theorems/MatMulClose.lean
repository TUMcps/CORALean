module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# A stored generator of a rounded matrix product is close to the exact one

Off by at most the gap between the two directed roundings. Stated over a family
of generators, as both polynomial representations store them; the gap is the
matrix `matMulDiff` of the generators laid out as columns, which is what
`generatorError` reads.

## Inputs
* `k` – number of columns
* `M` – matrix
* `A` – family of column vectors
* `i` – row index
* `l` – column index

## Hypotheses
* none

## Conclusion
* stored entry is within its gap of the exact product
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stored generator of a rounded product is off by at most the gap between the
two directed roundings. -/
theorem PolyZonotope.matMul_close {k : ℕ} (M : Mat 𝕋 m n) (A : Fin k → Vec 𝕋 n)
    (i : Fin m) (l : Fin k) : -- --- CONCL ---
    |(∑ r, toReal (M i r) * toReal (A l r)) - toReal (mulVecDown M (A l) i)|
      ≤ toReal (matMulDiff M (fun r l => A l r) i l) := by -- --- PROOF ---
  -- ascribed, so these are about `mulVecDown` and `matMulUp` rather than the `dot*` they unfold to
  have hlo : toReal (mulVecDown M (A l) i) ≤ ∑ r, toReal (M i r) * toReal (A l r) :=
    dotDown_le (M i) (A l)
  have hhi : ∑ r, toReal (M i r) * toReal (A l r)
      ≤ toReal (matMulUp M (fun r l => A l r) i l) :=
    le_dotUp (M i) (A l)
  have hgap := sub_le_subUp (matMulUp M (fun r l => A l r) i l) (mulVecDown M (A l) i)
  -- the gap's lower end is the stored generator's entry
  show _ ≤ toReal (subUp (matMulUp M (fun r l => A l r) i l) (mulVecDown M (A l) i))
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
