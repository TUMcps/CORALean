module

public import CORALean.ContDynamics.LinearARX.Operations.Alg2State

@[expose] public section

/-!
# Alg. 2: efficient reachability analysis

[1, Alg. 2], lines 9–11 of the `m`-th pass: `Ỹ_c ← S_c ⊕ T_c1`, `ỹ_v ← s_v + ∑_{i=0}^{p-1}
B̃ᵢ ũ_v(k₊ - i)`, `Ỹ(k:k₊) ← ỹ_v ⊕ Ỹ_c`. The constant part is only ever added to or moved
by `Ā_ext^p`, which is what keeps its cost linear in the horizon.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg2 (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (Uc : Set (Vec ℝ du)) (uv : ℕ → Vec ℝ du) (kinit m : ℕ) : Set (Vec ℝ (p * dy)) :=
  let state := sys.alg2State yinit Uc uv kinit m
  let k := state.1
  let kplus := k + p - 1
  let Sc := state.2.1
  let Tc1 := state.2.2.1
  let sv := state.2.2.2.2.1
  let Btilde := state.2.2.2.2.2
  let Yc := Sc + Tc1
  let yv := sv + ∑ i ∈ Finset.range p, Btilde i *ᵥ uv (kplus - i)
  {yv} + Yc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
