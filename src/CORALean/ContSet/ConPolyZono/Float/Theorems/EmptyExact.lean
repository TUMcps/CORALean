module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Empty

@[expose] public section

/-!
# `ConPolyZono.empty` denotes the empty set

The nominal part is `∅`: its single constraint row asks `1 ≤ (A μ)₀ ≤ 0`, and `one` and `zero`
read as `1` and `0`. So the sum with the error box is `∅` too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.empty_exact (n : ℕ) :
    (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  have hN : InflatedContSet.nominalSet (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, β, -, -, hsat, -⟩
    obtain ⟨h₁, h₂⟩ := hsat (0 : Fin 1)
    have hi : (InflatedContSet.nominal (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n))).b.inf
        (0 : Fin 1) = 1 := by
      rw [ConPolyZono.nominal_b]
      exact toReal_one
    have hs : (InflatedContSet.nominal (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n))).b.sup
        (0 : Fin 1) = 0 := by
      rw [ConPolyZono.nominal_b]
      exact toReal_zero
    rw [hi] at h₁
    rw [hs] at h₂
    linarith
  show InflatedContSet.nominalSet (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n))
      + (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)).err.construct = _
  rw [hN, Set.empty_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
