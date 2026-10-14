module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# CORA's ellipsoid-in-ellipsoid `contains_`, as printed

`@ellipsoid/private/priv_containsEllipsoid.m` (l. 46-96), reached from `contains_(E1, E2)` for
an ellipsoid `E2` that is not a point (l. 88-90): `H` and `G` are the generators of `E1` and
`E2` (`E.G` here, CORA's `U*sqrt(D)` of `svd(Q)`); if `rank(H) < n` and `rank([H G]) > rank(H)`
the answer is `false`; otherwise `Theta = pinv(H)*G`, `theta = pinv(H)*(q2 - q1)`, and the SDP
`min rho` s.t. `A - rho*B <= delta*C`, `delta >= 0` with `A = [Theta'Theta Theta'theta;
theta'Theta theta'theta]`, `B = diag(0, …, 0, 1)`, `C = diag(1, …, 1, -1)` decides by `rho <=
1 + tol`. The ranks are exact (`Matrix.rank`; CORA's `rank(·, tol)` agrees on the matrices of
the theorems); `pinv(H)` is the argument `Hp` and the solver (`value(rho)` after `optimize`) the
argument `sdp A B C`, each pinned down by hypotheses in the theorems. The rank test checks the
generators but not the centre offset `q2 - q1`, which `pinv(H)` projects away when `E1` is
degenerate; kept only so that `Ellipsoid.containsEllipsoidCora_counterexample` can state that
this is unsound.

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

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `priv_containsEllipsoid(E1, E2, tol)` as printed, `pinv(H)` being `Hp` and the SDP's
`value(rho)` being `sdp A B C`. -/
def Ellipsoid.containsEllipsoidCora (E₁ E₂ : Ellipsoid n) (Hp : Mat ℝ E₁.k n)
    (sdp : (A B C : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ) → ℝ) (tol : ℝ) : Prop :=
  let G := E₂.G
  let H := E₁.G
  let r := H.rank
  let r_comb := (Matrix.fromCols H G).rank
  if r < n ∧ r_comb > r then False else
    let Theta := Hp * G
    let theta : Mat ℝ E₁.k 1 := Hp * Matrix.of (fun i (_ : Fin 1) => (E₂.c - E₁.c) i)
    let A := Matrix.fromBlocks (Thetaᵀ * Theta) (Thetaᵀ * theta) (thetaᵀ * Theta) (thetaᵀ * theta)
    let B : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ := Matrix.fromBlocks 0 0 0 1
    let C : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ := Matrix.fromBlocks 1 0 0 (-1)
    let rho := sdp A B C
    rho ≤ 1 + tol

end CORALean.Real

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
