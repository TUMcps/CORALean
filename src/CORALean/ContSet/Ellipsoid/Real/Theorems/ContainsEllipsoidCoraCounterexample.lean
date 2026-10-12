import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsEllipsoidCora
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# CORA's ellipsoid-in-ellipsoid `contains_` accepts a disjoint degenerate ellipsoid

`E1 = ellipsoid(diag([1,0]))` is the segment `[-1, 1] × {0}`, `E2 = ellipsoid(diag([0.25,0]),
[0;1])` the segment `[-0.5, 0.5] × {1}`, disjoint from it. CORA's generators are `H = diag(1, 0)`
and `G = diag(0.5, 0)`; `rank([H G]) = rank(H) = 1`, so the rank test passes. `pinv(H) = H`
sends the offset `q2 - q1 = (0, 1)` to `theta = 0`, so `Theta = diag(0.5, 0)` and the SDP is
`min rho` s.t. `diag(Theta'Theta, -rho) <= delta*diag(1, 1, -1)`: its optimum is `rho = 1/4`, at
`delta = 1/4`, and CORA answers `true`.

`pinv(H)` is any `Hp` meeting the four Penrose equations (which force `Hp = H`); the SDP solver is
any function whose value on a problem bounded below is within `3/4` of every feasible `rho` — a
margin covering an inexact optimum. The fourth conjunct shows such a solver exists, so the
statement is not vacuous. Sign flips of CORA's `svd` columns leave `Theta'Theta` and `theta = 0`
unchanged. Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.containsEllipsoidCora_counterexample :
    let E₁ : Ellipsoid 2 := ⟨2, 0, !![1, 0; 0, 0]⟩
    let E₂ : Ellipsoid 2 := ⟨2, ![0, 1], !![1 / 2, 0; 0, 0]⟩
    let IsSdp := fun sdp : (A B C : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) → ℝ =>
      ∀ A B C, (∃ L, ∀ ρ δ : ℝ, 0 ≤ δ → (δ • C - (A - ρ • B)).PosSemidef → L ≤ ρ) →
        ∀ ρ δ : ℝ, 0 ≤ δ → (δ • C - (A - ρ • B)).PosSemidef → sdp A B C ≤ ρ + 3 / 4
    E₁.G * E₁.Gᵀ = !![1, 0; 0, 0] ∧ E₂.G * E₂.Gᵀ = !![1 / 4, 0; 0, 0] ∧
      ¬ E₂.construct ⊆ E₁.construct ∧ (∃ sdp, IsSdp sdp) ∧
      ∀ (Hp : Mat ℝ 2 2) sdp (tol : ℝ), E₁.G * Hp * E₁.G = E₁.G → Hp * E₁.G * Hp = Hp →
        (E₁.G * Hp)ᵀ = E₁.G * Hp → (Hp * E₁.G)ᵀ = Hp * E₁.G → IsSdp sdp → 0 ≤ tol →
        E₁.containsEllipsoidCora E₂ Hp sdp tol := by -- --- PROOF ---
  intro E₁ E₂ IsSdp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [E₁, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [E₂, Matrix.mul_apply, Fin.sum_univ_two]
  · -- the centre `(0, 1)` of `E₂` has second coordinate `1`, every point of `E₁` has `0`
    intro h
    obtain ⟨u, -, hu⟩ := h ⟨0, by rw [norm₂_zero]; norm_num, rfl⟩
    have := congrFun hu 1
    simp [E₁, E₂, dotProduct, Fin.sum_univ_two] at this
  · -- the infimum of the feasible values
    classical
    refine ⟨fun A B C => sInf {ρ | ∃ δ : ℝ, 0 ≤ δ ∧ (δ • C - (A - ρ • B)).PosSemidef}, ?_⟩
    intro A B C ⟨L, hL⟩ ρ δ hδ hpsd
    have : sInf {ρ | ∃ δ : ℝ, 0 ≤ δ ∧ (δ • C - (A - ρ • B)).PosSemidef} ≤ ρ :=
      csInf_le ⟨L, fun x ⟨δ', hδ', hp⟩ => hL x δ' hδ' hp⟩ ⟨δ, hδ, hpsd⟩
    show _ ≤ _
    linarith
  · intro Hp sdp tol h1 h2 h3 h4 hsdp htol
    -- the Penrose equations force `Hp = diag(1, 0)`
    have e1 := congrFun (congrFun h1 0) 0
    have e2 := congrFun (congrFun h2 1) 1
    have e3 := congrFun (congrFun h3 1) 0
    have e4 := congrFun (congrFun h4 0) 1
    simp only [E₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e1 e2 e3 e4
    simp at e1 e2 e3 e4
    have hHp : Hp = !![1, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> nlinarith
    subst hHp
    simp only [Ellipsoid.containsEllipsoidCora]
    rw [if_neg]
    · -- `(1/4, 1/4)` is feasible, and every feasible `rho` is at least `0`
      refine le_trans (hsdp _ _ _ ⟨0, fun ρ δ hδ hp => ?_⟩ (1 / 4) (1 / 4) (by norm_num) ?_) ?_
      · have := hp.diag_nonneg (i := Sum.inr 0)
        simp [E₁, E₂, Matrix.mul_apply, Fin.sum_univ_two, vecHead] at this
        linarith
      · have hd : (diagonal (Sum.elim ![(0 : ℝ), 1 / 4] ![0])).PosSemidef :=
          PosSemidef.diagonal (by intro i; rcases i with i | i <;> fin_cases i <;> simp)
        convert hd using 1
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
          norm_num [E₁, E₂, Matrix.mul_apply, Fin.sum_univ_two, vecHead,
            Matrix.diagonal_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]
      · linarith
    · -- `[H G] = H [I G]`, so its rank is at most that of `H`
      rintro ⟨-, hr⟩
      have hfac : Matrix.fromCols E₁.G E₂.G = E₁.G * Matrix.fromCols (1 : Mat ℝ 2 2) E₂.G := by
        rw [Matrix.mul_fromCols, Matrix.mul_one]
        congr 1
        ext i j; fin_cases i <;> fin_cases j <;> simp [E₁, E₂, Matrix.mul_apply, Fin.sum_univ_two]
      have := Matrix.rank_mul_le_left E₁.G (Matrix.fromCols (1 : Mat ℝ 2 2) E₂.G)
      rw [← hfac] at this
      exact absurd hr (not_lt.2 this)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
