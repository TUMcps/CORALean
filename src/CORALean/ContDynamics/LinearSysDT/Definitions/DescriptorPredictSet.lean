module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The uncertain state set of a descriptor system

[1, Def. 1]: for `E x_{k+1} = A x_k + B u_k + D ω_k + D_d d_k` [1, Eq. 4], with `ω_k` in the
unit box `W = ⟨0, I⟩` and `d_k` an unknown input with no bound, the states `x` with
`E x ∈ A X̄₋ ⊕ B u₋ ⊕ D_d d ⊕ D W` for the previous set `X̄₋`. The paper writes `D_d d` for
an unknown `d`; read here as some `d`, every unknown input being possible. `E` may be
singular, so the set is given by the equation it satisfies, not by a map.

## Inputs
* `E` – descriptor matrix
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `Dd` – unknown input matrix
* `Xprev` – previous state set
* `u` – previous input

## Output
* the states consistent with the dynamics over every unknown input

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n nu nw nd : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{x | E x ∈ A X̄₋ ⊕ B u ⊕ D_d d ⊕ D W}`, over every `d`. -/
def LinearSysDT.descriptorPredictSet (E A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nw)
    (Dd : Mat ℝ n nd) (Xprev : Set (Vec ℝ n)) (u : Vec ℝ nu) : Set (Vec ℝ n) :=
  {x | ∃ xprev ∈ Xprev, ∃ ω : Vec ℝ nw, (∀ i, |ω i| ≤ 1) ∧ ∃ d : Vec ℝ nd,
    E *ᵥ x = A *ᵥ xprev + B *ᵥ u + Dd *ᵥ d + D *ᵥ ω}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
