import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `LinearReset.synchronize` in directed rounding

The sum of the components' matrices and offsets, `A = ΣW_i + diag(id)`, `c = Σw_i`, is not exact at
a float, so it is returned as two matrices and two vectors: lower and upper entry bounds, each
sum rounded in its own direction (`sumDown`, `sumUp`; the added `1` is exact). Soundness is
`LinearReset.synchronizeFloat_outer`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower and upper bounds of `A` and of `c`: `((A_lo, A_hi), (c_lo, c_hi))`. -/
def LinearReset.synchronizeFloat (W : Fin k → Mat 𝕋 n n) (w : Fin k → Vec 𝕋 n)
    (idStates : Finset (Fin n)) : (Mat 𝕋 n n × Mat 𝕋 n n) × (Vec 𝕋 n × Vec 𝕋 n) :=
  let diag : Fin n → Fin n → 𝕋 := fun i l => if i = l ∧ i ∈ idStates then one else zero
  ((fun i l => addDown (sumDown fun j => W j i l) (diag i l),
    fun i l => addUp (sumUp fun j => W j i l) (diag i l)),
   (fun i => sumDown fun j => w j i, fun i => sumUp fun j => w j i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
