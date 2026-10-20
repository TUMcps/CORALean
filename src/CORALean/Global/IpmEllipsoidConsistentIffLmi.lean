module

public import CORALean.Global.IpmEllipsoidEq
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Consistency of the ellipsoid predictor as linear matrix inequalities

[1, Sec. 3 (Problem 1.b)]: for the ellipsoid class [1, Eq. 9] with `μ_Q = Tr[PW] + γ²`, Problem 1 is
the semidefinite program with slack variables `ϵ₁, …, ϵ_N`, `P ≻ 0`, `[γ² ϵ_t; ϵ_t 1] ⪰ 0` and
`[ϕ(t)ᵀPϕ(t), y(t) - cᵀϕ(t) - ϵ_t; y(t) - cᵀϕ(t) - ϵ_t, 1] ⪰ 0`. The cost is the same in both, so
the claim is that the constraints have the same feasible `(c, P, γ)`. They do: a `2 × 2` matrix
`[a b; b 1]` is positive semidefinite exactly when `b² ≤ a`, so the two inequalities say `|ϵ_t| ≤ γ`
and `|y(t) - cᵀϕ(t) - ϵ_t| ≤ √(ϕ(t)ᵀPϕ(t))`. Some `ϵ_t` satisfies both iff
`|y(t) - cᵀϕ(t)| ≤ √(ϕ(t)ᵀPϕ(t)) + γ`, which is `y(t) ∈ I(ϕ(t))` by [1, Eq. 7] (`ipmEllipsoid_eq`).
The program's variable is `γ²`, and `γ = √(γ²) ≥ 0`.

## Inputs
* `c` – center of the parameter ellipsoid
* `P` – shape matrix of the ellipsoid
* `γ` – noise bound
* `ϕ` – regressor data
* `y` – observed outputs

## Hypotheses
* `hP` – the shape matrix is positive definite
* `hγ` – the noise bound is nonnegative

## Conclusion
* the data are consistent exactly when slack variables satisfy the two matrix inequalities

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `[a b; b 1] ⪰ 0` iff `b² ≤ a`: the Schur complement of the corner `1`. -/
theorem aux_posSemidef_two_iff (a b : ℝ) :
    (!![a, b; b, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ↔ b ^ 2 ≤ a := by -- --- PROOF ---
  rw [posSemidef_iff_dotProduct_mulVec]
  have hH : (!![a, b; b, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  -- the quadratic form, written out
  have hq : ∀ x : Fin 2 → ℝ, star x ⬝ᵥ ((!![a, b; b, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x)
      = a * x 0 ^ 2 + 2 * b * x 0 * x 1 + x 1 ^ 2 := fun x => by
    simp [dotProduct, mulVec, Fin.sum_univ_two]; ring
  constructor
  · rintro ⟨-, h⟩
    -- at `x = (1, -b)` the form is `a - b²`
    have := h ![1, -b]
    rw [hq] at this
    simp at this
    nlinarith
  · intro h
    refine ⟨hH, fun x => ?_⟩
    rw [hq]
    nlinarith [sq_nonneg (x 1 + b * x 0), sq_nonneg (x 0)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (Problem 1.b)]: the ellipsoid predictor is consistent with the data iff slack
variables `ϵ_t` satisfy the program's two linear matrix inequalities at every `t`. -/
theorem ipmEllipsoid_consistent_iff_lmi (c : Vec ℝ n) (P : Mat ℝ n n) (hP : P.PosDef) (γ : ℝ)
    (hγ : 0 ≤ γ) (ϕ : Fin N → Vec ℝ n) (y : Fin N → ℝ) : -- --- CONCL ---
    (∀ t, y t ∈ ipmEllipsoid c P γ (ϕ t)) ↔
      ∃ ϵ : Fin N → ℝ, ∀ t, (!![γ ^ 2, ϵ t; ϵ t, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧
        (!![ϕ t ⬝ᵥ (P *ᵥ ϕ t), y t - c ⬝ᵥ ϕ t - ϵ t; y t - c ⬝ᵥ ϕ t - ϵ t, 1]
          : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by -- --- PROOF ---
  simp only [aux_posSemidef_two_iff, ipmEllipsoid_eq c P hP γ hγ, Set.mem_Icc]
  -- `ϕᵀPϕ ≥ 0`, so its square root squares back to it
  have ha : ∀ t, 0 ≤ ϕ t ⬝ᵥ (P *ᵥ ϕ t) := fun t => by
    simpa using hP.posSemidef.dotProduct_mulVec_nonneg (ϕ t)
  constructor
  · intro h
    -- the slack: the residual clamped to `[-γ, γ]`
    refine ⟨fun t => max (-γ) (min γ (y t - c ⬝ᵥ ϕ t)), fun t => ⟨?_, ?_⟩⟩
    · have h1 : -γ ≤ max (-γ) (min γ (y t - c ⬝ᵥ ϕ t)) := le_max_left _ _
      have h2 : max (-γ) (min γ (y t - c ⬝ᵥ ϕ t)) ≤ γ := max_le (by linarith) (min_le_left _ _)
      nlinarith
    · obtain ⟨h1, h2⟩ := h t
      have hs := Real.sq_sqrt (ha t)
      have hs0 := Real.sqrt_nonneg (ϕ t ⬝ᵥ (P *ᵥ ϕ t))
      -- the residual left after the slack is within `±√(ϕᵀPϕ)`
      have hr : |y t - c ⬝ᵥ ϕ t - max (-γ) (min γ (y t - c ⬝ᵥ ϕ t))|
          ≤ Real.sqrt (ϕ t ⬝ᵥ (P *ᵥ ϕ t)) := by
        rw [abs_le]
        constructor
        · rcases le_total (y t - c ⬝ᵥ ϕ t) γ with hd | hd
          · rw [min_eq_right hd]
            rcases le_total (-γ) (y t - c ⬝ᵥ ϕ t) with he | he
            · rw [max_eq_right he]; linarith
            · rw [max_eq_left he]; linarith
          · rw [min_eq_left hd, max_eq_right (by linarith)]; linarith
        · rcases le_total (y t - c ⬝ᵥ ϕ t) γ with hd | hd
          · rw [min_eq_right hd]
            rcases le_total (-γ) (y t - c ⬝ᵥ ϕ t) with he | he
            · rw [max_eq_right he]; linarith
            · rw [max_eq_left he]; linarith
          · rw [min_eq_left hd, max_eq_right (by linarith)]; linarith
      rw [← hs]
      exact sq_le_sq' (abs_le.mp hr).1 (abs_le.mp hr).2
  · rintro ⟨ϵ, h⟩ t
    obtain ⟨h1, h2⟩ := h t
    -- `ϵ² ≤ γ²` and `r² ≤ ϕᵀPϕ` give `|ϵ| ≤ γ` and `|r| ≤ √(ϕᵀPϕ)`
    have he : |ϵ t| ≤ γ := abs_le_of_sq_le_sq' h1 hγ |> fun h => abs_le.mpr h
    have hr : |y t - c ⬝ᵥ ϕ t - ϵ t| ≤ Real.sqrt (ϕ t ⬝ᵥ (P *ᵥ ϕ t)) :=
      Real.abs_le_sqrt h2
    obtain ⟨he1, he2⟩ := abs_le.mp he
    obtain ⟨hr1, hr2⟩ := abs_le.mp hr
    constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
