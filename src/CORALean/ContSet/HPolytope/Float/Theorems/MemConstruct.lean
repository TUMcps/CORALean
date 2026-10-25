module

public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIffExact

@[expose] public section

/-!
# Membership in an error-free float halfspace description, in the stored fields

What an error-free polytope denotes is its nominal part, the exact layer's `ineqs` intersected
with its `eqs`, so membership arrives as a nesting of three lemmas. This unfolds it once into the
two blocks the stored matrices state: a bound per inequality row, and a value per equality row.

It is the form every operation and every conversion at this layer states its obligation in. A
polytope that carries an error box reads through `HPolytope.mem_rows_of_mem_construct` instead,
which gives the rows with the box folded in.

## Inputs
* `P` – H-polytope
* `x` – point of length `n`

## Hypotheses
* `hP` – `P.IsErrFree`

## Conclusion
* `x` lies in an error-free polytope iff it meets every inequality and equality as stored
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       04-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_construct_iff [SoundFloatArithmetic 𝕋] {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (hP : P.IsErrFree) {x : Vec ℝ n} : -- --- CONCL ---
    x ∈ P.construct ↔
      (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
        ∧ ∀ i, (toRealMat P.Ae *ᵥ x) i = toReal (P.be i) := by -- --- PROOF ---
  rw [HPolytope.construct_eq_nominal hP.1]
  exact HPolytope.mem_nominal_iff_exact hP.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
