import CORALean.ContSet.SetUnion.SetUnion

/-!
# `SetUnion.mtimes`

Maps `Mtimes.mtimes` over every branch, at whatever family carries it: the
image of a union is the union of the images, so multiplying each branch and
re-collecting keeps the shape a union already has.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
  [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `M` applied to every branch. -/
def SetUnion.mtimes {m n : ℕ} (M : 𝕄 m n) (u : SetUnion (S n)) : SetUnion (S m) :=
  ⟨u.sets.map (Mtimes.mtimes M)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
