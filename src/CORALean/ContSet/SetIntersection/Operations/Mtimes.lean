import CORALean.ContSet.SetIntersection.SetIntersection

/-!
# `SetIntersection.mtimes`

Maps `Mtimes.mtimes` over every branch, at whatever family carries it — the
image of an intersection sits inside the intersection of the images, never
equal to it in general, so this is the outer construction the intersection
side of the tree already expects.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
  [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `M` applied to every branch. At `sets = []` the branch list stays empty,
so `construct` stays `univ` on both sides of the guarantee. -/
def SetIntersection.mtimes {m n : ℕ} (M : 𝕄 m n) (I : SetIntersection (S n)) :
    SetIntersection (S m) :=
  ⟨I.sets.map (Mtimes.mtimes M)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
