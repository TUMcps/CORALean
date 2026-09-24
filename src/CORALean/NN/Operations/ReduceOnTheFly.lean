import CORALean.NN.Operations.ReduceOnTheFlyFrom

/-!
# [1, Alg. 2]: reducing a network on the fly

[1, Alg. 2] walks the nonlinear layers `k = 2, 4, …, κ` of a `ReducibleNetwork`, reducing
each against the set that actually reaches it, and returns the reduced network `Φ̂_ρ` with
the output set `Y = H_κ` it computed on the way. Written once over the scalar: at a machine
scalar it runs, the look-ahead boxes and [1, Prop. 4]'s error boxes rounding outward.

`reduceOnTheFly_outer` is its soundness at every instance of the network, and
`Real.reduceOnTheFly_reducesAt` puts what it returns at `𝕋 := ℝ` in `ReducesAt`.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float ContSet IntervalOuter

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the network `Φ` reduced at rate `ρ` along the input set `X`, and the output
set `Y` it computes on the way; `none` where [1, Alg. 1] ran out of `fuel` at some layer. -/
def reduceOnTheFly (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) {n m : ℕ} (X : S n) (ρ : 𝕋) :
    ReducibleNetwork 𝕋 n m → Option (ReducibleNetwork 𝕋 n m × S m)
  | .nil => some (.nil, X)                                          -- κ = 0: no layer to reduce
  | .cons L_1 L_2 B rest =>
    let H_0 := X                                                    -- Alg. 2, line 1
    let Lhat_1 := L_1                                               -- Alg. 2, line 1
    reduceOnTheFlyFrom le tol fuel ρ H_0 Lhat_1 L_2 B rest          -- Alg. 2, lines 2-13

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
