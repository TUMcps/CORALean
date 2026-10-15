module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet
public import CORALean.Global.SupportFunction.Composition

@[expose] public section

/-!
# A support witness propagated along the steps

The dual of `ReachSetBound`, by the same two-line recursion — `image` for the
matrix, `add` for the input set — but for a lower bound carrying the point that
attains it. This is the CORALean counterpart of `Alg. 1` of [1]'s
verify-or-falsify loop: a lower bound on the support function of the reachable
set is that paper's novel contribution, obtained from support vectors of an
inner approximation, which is exactly what a `SupportWitness` carries [1, Alg. 1 (lower bounds)].

As with `reachSetBound`, the hypotheses are functions of a direction rather
than two numbers, so any representation that can answer `SupportWitness` for
itself may be handed in and none is named here.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A witness for `R₀` and one for `U`, in every direction, give a witness for
the set reached after `k` steps — no set built, and `reach` never mentioned. -/
def LinearSysDT.reachSetWitness (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness (construct R₀) d)
    (bU : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness (construct U) d) :
    (k : ℕ) → (c : Vec ℝ n →ₗ[ℝ] ℝ) → SupportWitness (sys.reachSet R₀ U k) c
  | 0, c => b₀ c
  | k + 1, c =>
    (SupportWitness.image (mulVecLin (toRealMat sys.A))
      (sys.reachSetWitness R₀ U b₀ bU k (c.comp (mulVecLin (toRealMat sys.A))))).add (bU c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
