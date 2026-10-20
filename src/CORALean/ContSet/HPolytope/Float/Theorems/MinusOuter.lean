module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.TranslateOuter

@[expose] public section

/-!
# `HPolytope.minus` encloses

Every point of the polytope less the subtrahend lies in the result: negation is
exact, so this is `translate_outer` at `-v`.

## Inputs
* `P` – H-polytope
* `v` – vector of length `n`

## Hypotheses
* none

## Conclusion
* the image of `P` shifted by `-v` is contained in `P.minus v`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minus_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) : -- --- CONCL ---
    (· - toRealVec v) '' P.construct ⊆ (P.minus v).construct := by -- --- PROOF ---
  have h := HPolytope.translate_outer (-v) P
  have hneg : toRealVec (-v) = -toRealVec v := toRealVec_neg _
  rw [hneg] at h
  show _ ⊆ (HPolytope.translate (-v) P).construct
  simpa only [sub_eq_add_neg, add_comm _ (-toRealVec v)] using h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
