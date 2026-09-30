import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The settings of a discrete-time linear backward reach, `∀` reading

The two things the computed backward set runs on besides the target and the
input set: `Ainv`, the inverse the sets are carried back along, and `diff`, the
set difference that removes the input at every step, `none` where it cannot
certify one.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- The inverse `Ainv` and the difference `diff` a `∀` backward reach is run
with. -/
structure LinearSysDT.BackReachForallOptions (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type) (n : ℕ) where
  Ainv : Mat 𝕋 n n
  diff : S n → S n → Option (S n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
