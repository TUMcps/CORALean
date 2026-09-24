import CORALean.NN.Theorems.ReduceOnTheFlyOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# [1, Thm. 1] for what [1, Alg. 2] actually returns

[1, Thm. 1]: given an input set `X`, a network `Φ` and a reduction rate `ρ`, [1, Alg. 2]
constructs a reduced network `Φ̂_ρ` for which verification entails verifying `Φ` — checking
a specification on the output set `Y` the algorithm computed is checking it on `Φ(X)`.
`reduceOnTheFly_outer` is the inclusion and `holds_of_outer` the rest. It holds at every
scalar, `le`, `tol`, `fuel` and `ρ`, and at every instance of a network in [1, Eq. 2]'s form,
the original network — every `I' = [0, 0]` — being the one [1] means.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a specification holding on the output set `Y` of [1, Alg. 2] holds on the
original network's exact image of `X`. -/
theorem holds_of_reduceOnTheFly {le : 𝕋 → 𝕋 → Bool} {tol : 𝕋} {fuel : ℕ} {ρ : 𝕋} {n m : ℕ}
    {X : S n} {Φ Φhat : ReducibleNetwork 𝕋 n m} {Y : S m} {f : Vec ℝ n → Vec ℝ m}
    (hΦ : Φ.Instance f) (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y))
    {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]
    (spec : Specification ContSet) (hspec : spec.Holds (construct Y)) :
    spec.Holds (f '' construct X) :=
  spec.holds_of_outer (reduceOnTheFly_outer hΦ hrun).1 hspec

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
