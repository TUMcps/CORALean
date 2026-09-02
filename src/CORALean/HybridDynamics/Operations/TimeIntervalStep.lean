import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Location

/-!
# `Location.timeIntervalStep`

`LinearSys.timeIntervalStep` on the location's own dynamics, and nothing more —
no new computation, only a name that carries the representation.

That is the whole point of it: `ℓ.dynamics : LinearSys 𝕋 n` drops `S`, so a use
site stating the enclosure has to write `(S := 𝒵)` even though `ℓ` already
pinned the family. Read off `ℓ` instead, the family comes with the location.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]

/-- The enclosure of a stay of length `r`, at Taylor order `η`. -/
noncomputable def Location.timeIntervalStep (ℓ : Location S L 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ : S n) : S n :=
  ℓ.dynamics.timeIntervalStep r η X₀

end CORALean.Real
