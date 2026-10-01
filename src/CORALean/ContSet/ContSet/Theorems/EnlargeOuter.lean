import CORALean.ContSet.ContSet.Operations.Enlarge
import CORALean.ContSet.ContSet.Theorems.MinusOuter
import CORALean.ContSet.ContSet.Theorems.TimesOuter

/-!
# `enlarge` encloses the scaling about the centre
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recentre (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `c + f ⊙ (x - c)`, `x` in `S`, `c` its centre and `f` read as reals, is in
`enlarge S f`: `minus_outer`, `times_outer` and `plus_outer` in turn. -/
theorem ContSet.enlarge_outer (s : S n) (f : Vec 𝕋 n) :
    (fun x : Vec ℝ n => Recentre.centre s + fun i => toReal (f i) * (x i - Recentre.centre s i)) ''
      construct s ⊆ construct (ContSet.enlarge s f) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  have h1 := ContSet.minus_outer s (Recentre.centre s) ⟨x, hx, rfl⟩
  have h2 := ContSet.times_outer f (ContSet.minus s (Recentre.centre s))
    ⟨x - Recentre.centre s, h1, rfl⟩
  exact Plus.plus_outer _ _ ⟨_, h2, Recentre.centre s, OfPoint.mem_ofPoint _, add_comm _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
