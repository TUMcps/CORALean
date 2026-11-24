module

public import CORALean.ContSet.Taylm.Float.Operations.FromRange
public import CORALean.ContSet.Taylm.Float.Theorems.ConstSparseOuter

@[expose] public section

/-!
# `Taylm.fromRange` encloses every number of its box

The midpoint `m` is half the sum rounded up, so `v - m` lies within the half-width plus half the
gap between the two roundings of the sum, which the remainder and the error box hold.

## Inputs
* `n` – number of variables
* `lo` – lower end of the box
* `hi` – upper end of the box
* `N` – the order `times` truncates to
* `v` – a number

## Hypotheses
* `hlo` – `v` is at least `lo`
* `hhi` – `v` is at most `hi`

## Conclusion
* the model encloses the constant function `v`
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.fromRange_outer (n : ℕ) (lo hi : 𝕋) (N : ℕ) {v : ℝ} (hlo : toReal lo ≤ v)
    (hhi : v ≤ toReal hi) : -- --- CONCL ---
    (Taylm.fromRange n lo hi N).Encloses fun _ => v := by -- --- PROOF ---
  intro t _
  obtain ⟨hp, -⟩ := (Taylm.constSparse_outer n (half (addUp lo hi)) N).2 t
  -- the polynomial is the stored midpoint, the half-sum rounded up
  have hpoly : (Taylm.fromRange n lo hi N).inflated.poly t = toReal (addUp lo hi) / 2 := by
    rw [← toReal_half]; exact hp
  rw [hpoly]
  have h1 := add_le_addUp lo hi
  have h2 := addDown_le_add lo hi
  have h3 := add_le_addUp hi (neg lo)
  have h4 := add_le_addUp (addUp lo hi) (neg (addDown lo hi))
  simp only [Taylm.fromRange, Taylm.inflated, toReal_neg, toReal_half, subUp,
    toReal_neg] at h3 h4 ⊢
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
