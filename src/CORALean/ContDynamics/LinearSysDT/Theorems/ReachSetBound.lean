import CORALean.ContDynamics.LinearSysDT.ReachSet
import CORALean.Global.LinProg.API

/-!
# A support bound propagated along the steps

The whole recursion is two lines of `Global.LinProg.Composition`: `image` for
the matrix and `add` for the input set. `image` is the one that carries the
matrix, and it does so by moving the *direction* — the value is unchanged and
`c` becomes `c ∘ A` — so what a caller must be able to answer is one direction
per step, `c ∘ Aᵏ` at the initial set and `c ∘ Aⁱ` at the input set.

That is why the hypotheses are functions of a direction rather than two numbers:
every `supportBound` this tree defines already has that shape, `Ellipsoid`,
`Interval`, `Zonotope`, `VPolytope` and `Capsule` alike, so any of them may be
handed in and none is named here.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A bound on `R₀` and one on `U`, in every direction, give a bound on the set
reached after `k` steps — no set built, and `reach` never mentioned. -/
def LinearSysDT.reachSetBound (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bU : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct U) d) :
    (k : ℕ) → (c : Vec ℝ n →ₗ[ℝ] ℝ) → SupportBound (sys.reachSet R₀ U k) c
  | 0, c => b₀ c
  | k + 1, c =>
    (SupportBound.image (mulVecLin (toRealMat sys.A))
      (sys.reachSetBound R₀ U b₀ bU k (c.comp (mulVecLin (toRealMat sys.A))))).add (bU c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
