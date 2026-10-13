import CORALean.ContDynamics.LinearSys.Operations.MinBackReachSupportFloat

/-!
# `Alg. 1` lines 4 and 14 in floats: the accumulated support value

`minBackReachP` computed in `𝕋`: [1, Alg. 1] lines 4 and 14, `p_(j)` after the steps `0` to `k`.
`maximum`, not line 14's `min` — a union's support is the largest of its parts', as over `ℝ` — and
exact, since choosing between two floats rounds nothing.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4 and 14: `p_(j)` after the steps `0` to `k`. -/
def LinearSys.minBackReachPFloat (sys : LinearSys 𝕋 n) (CZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (W₀ U₀ : Zonotope (Vec 𝕋 n)) (Zw : 𝕋 → Zonotope (Vec 𝕋 n)) (N : Mat 𝕋 q n)
    (t₀ Δt : 𝕋) (η ν : ℕ) :
    ℕ → Fin q → 𝕋
  | 0 => fun j => sys.minBackReachSupportFloat CZ W₀ U₀ Zw N t₀ Δt η ν 0 j
  | k + 1 => fun j => maximum (sys.minBackReachPFloat CZ W₀ U₀ Zw N t₀ Δt η ν k j)
      (sys.minBackReachSupportFloat CZ W₀ U₀ Zw N t₀ Δt η ν (k + 1) j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
