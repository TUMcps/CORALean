module

public import CORALean.ContSet.Zonotope.Real.Operations.BackReachAligned

@[expose] public section

/-!
# `Zonotope.backReachAligned_h`

[1, Sec. IV-B]: `N_{k+1} = N_k + N_U`, a step keeps `Z_k`'s generators (the aligned
difference subtracts generator-wise) and adds `U`'s. `rfl` through the definition.

## Inputs
* `A` – state matrix
* `B` – input matrix
* `K` – constant offset vector
* `U` – input zonotope
* `Z₀` – initial zonotope
* `σ` – alignment-direction selector
* `k` – step count

## Hypotheses
* none

## Conclusion
* generator count grows by that of `U` per step

## References

* [1] [L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters,
      2022.](../../../../../../../../references/2022/yang-lcss-zonotopic-underapproximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-B]: each step adds `U`'s generator count. -/
theorem Zonotope.backReachAligned_h (A : Mat ℝ n n) (B : Mat ℝ n m) (K : Vec ℝ n)
    (U : Zonotope (Vec ℝ m)) (Z₀ : Zonotope (Vec ℝ n))
    (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ)) (k : ℕ) :
    (Zonotope.backReachAligned A B K U Z₀ σ (k + 1)).h
      = (Zonotope.backReachAligned A B K U Z₀ σ k).h + U.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
