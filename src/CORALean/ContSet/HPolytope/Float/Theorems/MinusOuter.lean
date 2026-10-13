import CORALean.ContSet.HPolytope.Float.Operations.Minus
import CORALean.ContSet.HPolytope.Float.Operations.TranslateOuter

/-!
# `HPolytope.minus` encloses

Every point of the polytope less the subtrahend lies in the result: negation is
exact, so this is `translate_outer` at `-v`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minus_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) :
    (· - toRealVec v) '' P.construct ⊆ (P.minus v).construct := by -- --- PROOF ---
  have h := HPolytope.translate_outer (fun i => neg (v i)) P
  have hneg : toRealVec (fun i => neg (v i)) = -toRealVec v := by
    funext i
    simp [toRealVec, toReal_neg]
  rw [hneg] at h
  show _ ⊆ (HPolytope.translate (fun i => neg (v i)) P).construct
  simpa only [sub_eq_add_neg, add_comm _ (-toRealVec v)] using h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
