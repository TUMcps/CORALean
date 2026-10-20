module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The canonical form's input term is the input

At `LinearSys.canonicalFloat A`, `B = I` and `c = 0`, so the input term `B u + c` of the full
equation is `u` itself, after rounding nothing: `toReal one = 1` and `toReal zero = 0`. What the
float reaches read off the system (`inputSetFloat`) is then the input set unchanged.

## Inputs
* `A` – float system matrix

## Hypotheses
* none

## Conclusion
* the canonical form's input term is the identity map
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalFloat_input (A : Mat 𝕋 n n) : -- --- CONCL ---
    (fun u => Scalar.toRealMat (LinearSys.canonicalFloat A).B *ᵥ u +
      Scalar.toRealVec (LinearSys.canonicalFloat A).c) = id := by -- --- PROOF ---
  funext u i
  show ∑ j, toReal (if i = j then (one : 𝕋) else zero) * u j + toReal (zero : 𝕋) = u i
  rw [toReal_zero, add_zero, Finset.sum_eq_single i]
  · rw [if_pos rfl, toReal_one, one_mul]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
