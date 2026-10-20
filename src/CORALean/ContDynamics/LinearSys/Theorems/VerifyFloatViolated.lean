module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyFloat
public import CORALean.ContDynamics.LinearSys.Theorems.NotVerifySpecFloatOfVerifyRunFloat

@[expose] public section

/-!
# `verifyFloat` returning `false` refutes the specification

[1, Alg. 3]: under the same hypotheses, `some false` from `verifyFloat` gives a reached state that
violates a safe or an unsafe set.

## Inputs
* `Reach` – reachable set
* `reachFn` – float reachable set as a function of the error
* `innerApprox` – float inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – float safe polytopes
* `F` – float unsafe polytopes
* `εmax₀` – float initial maximal error
* `fuel` – number of iterations

## Hypotheses
* `h` – the oracles are sound
* `hv` – the verification answers false

## Conclusion
* the specification does not hold

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyFloat_violated
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.VerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax₀ : 𝕋) (fuel : ℕ)
    (hv : LinearSys.verifyFloat reachFn innerApprox distG distF G F εmax₀ fuel = some false)
    : -- --- CONCL ---
    ¬ LinearSys.VerifySpecFloat G F Reach :=
  LinearSys.not_verifySpecFloat_of_verifyRunFloat h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
