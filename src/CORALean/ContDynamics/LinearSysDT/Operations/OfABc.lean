module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# CORA's `linearSysDT(A, B, c, dt)`

The system CORA's constructor builds from `A`, `B`, `c` and the sampling time `dt` alone,
every other matrix at its default [1]: the output is the state (`C = I`, `D = 0`, `k = 0`), and
one disturbance and one noise enter through the zero columns `E = 0`, `F = 0`. It is what
CORA's `identify` returns (`priv_identifyDMD`).

## Inputs
* `A` – state matrix
* `B` – input matrix
* `c` – offset
* `dt` – sampling time

## Output
* the discrete-time system with default output and disturbance matrices

## References

* [1] `contDynamics/@linearSysDT/linearSysDT.m`, `aux_computeProperties`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ} {𝕋 : Type} [Zero 𝕋] [One 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linearSysDT(A, B, c, dt)`: `(A, B, c, I, 0, 0, 0, 0)`, one disturbance and one noise. -/
def LinearSysDT.ofABc (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (c : Vec 𝕋 n) (dt : 𝕋) : LinearSysDT 𝕋 n :=
  ⟨m, n, 1, 1, A, B, c, 1, 0, 0, 0, 0, dt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
