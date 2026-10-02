import CORALean.Global.Float.SoundFloatArithmetic

/-!
# A directed power

`Bᵏ` rounded up, by repeated `mulUp`. An upper bound on `xᵏ` for every `0 ≤ x ≤ B`, which
is what a Lagrange remainder `|f - c|ᴺ⁺¹` needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def powUp (B : 𝕋) : ℕ → 𝕋
  | 0 => one
  | k + 1 => mulUp (powUp B k) B

theorem le_powUp [SoundFloatArithmetic 𝕋] {B : 𝕋} {x : ℝ} (hx : 0 ≤ x) (hB : x ≤ toReal B) :
    ∀ k : ℕ, x ^ k ≤ toReal (powUp B k) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => simp [powUp, toReal_one]
  | succ k ih =>
    rw [pow_succ, powUp]
    exact le_trans (mul_le_mul ih hB hx (le_trans (pow_nonneg hx k) ih)) (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
