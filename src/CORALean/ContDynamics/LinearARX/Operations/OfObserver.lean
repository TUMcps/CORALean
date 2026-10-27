module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# From a state-space model to an ARMAX model

[1, Prop. 2], (5): with a deadbeat observer gain `M`, `(A + MC)^p = 0`, the model
`x(k+1) = A x(k) + B̃ ũ(k)`, `y(k) = C x(k) + D̃ ũ(k)` has `Ā_i = -C(A + MC)^{i-1} M`,
`B̄₀ = D̃` and `B̄ᵢ = C(A + MC)^{i-1}(B̃ + M D̃)`. `B̃`, `D̃` are the combined input matrices;
[1]'s `[B I 0]`, `[D 0 I]` for `ũ = (u, w, v)` are one choice of them. As everywhere in
this structure, `Abar i` is `Ā_{i+1}` and `Bbar j` is `B̄_j`.

## Inputs
* `p` – number of lags
* `A` – state matrix
* `Bu` – input matrix
* `C` – output matrix
* `Du` – feedthrough matrix
* `M` – deadbeat observer gain
* `dt` – sampling time

## Output
* the ARX system from the observer form

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n dy du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.ofObserver (p : ℕ) (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) (M : Mat ℝ n dy) (dt : ℝ) : LinearARX ℝ dy du p where
  Abar i := -(C * (A + M * C) ^ (i : ℕ) * M)
  Bbar j := if (j : ℕ) = 0 then Du else C * (A + M * C) ^ ((j : ℕ) - 1) * (Bu + M * Du)
  dt := dt                                                          -- obj.dt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
