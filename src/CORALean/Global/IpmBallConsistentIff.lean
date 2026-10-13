module

public import CORALean.Global.IpmBallEq

@[expose] public section

/-!
# Consistency of the ball predictor is linear

[1, Sec. 3], Problem 1.a: for the ball class [1, Eq. 8] with cost `μ_Q = αr + γ` [1, Eq. 10],
Problem 1 becomes a linear program: the predictor `I_{c,r,γ}` is consistent with the data
`(ϕ(t), y(t))`, `y(t) ∈ I(ϕ(t))` for every `t` ([1, Def. 2]), exactly when
`cᵀϕ(t) - r‖ϕ(t)‖ - γ ≤ y(t) ≤ cᵀϕ(t) + r‖ϕ(t)‖ + γ` for every `t`, which with the data fixed is
linear in `(c, r, γ)`, and `r, γ ≥ 0`. By [1, Eq. 6] (`ipmBall_eq`).

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipmBall_consistent_iff (c : Vec ℝ n) (r γ : ℝ) (hr : 0 ≤ r) (hγ : 0 ≤ γ)
    (ϕ : Fin N → Vec ℝ n) (y : Fin N → ℝ) :
    (∀ t, y t ∈ ipmBall c r γ (ϕ t)) ↔
      ∀ t, c ⬝ᵥ ϕ t - r * Real.sqrt (ϕ t ⬝ᵥ ϕ t) - γ ≤ y t ∧
        y t ≤ c ⬝ᵥ ϕ t + r * Real.sqrt (ϕ t ⬝ᵥ ϕ t) + γ := by -- --- PROOF ---
  refine forall_congr' fun t => ?_
  rw [ipmBall_eq c r γ hr hγ, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
