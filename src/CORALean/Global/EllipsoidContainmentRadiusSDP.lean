module

public import CORALean.Global.DmdPinv
public import CORALean.Global.SLemmaPosSemidef
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section

/-!
# The ellipsoid-in-ellipsoid containment radius as a semidefinite program

[1, Thm. 13]: for `Ê = E₂(G, c)` and a non-degenerate `E = E₂(H, d)`,
`r(Ê, E) = √(min_{ρ ∈ S} ρ)`, `S` the `ρ` with
`[[ΘᵀΘ, Θᵀθ], [θᵀΘ, θᵀθ]] - ρ [[0, 0], [0, 1]] ⪯ δ [[I, 0], [0, -1]]` (Eq. 23) for some
`δ ≥ 0`, `Θ = H⁺G`, `θ = H⁺(c - d)`. Non-degenerate is `H` onto; `H⁺` is any matrix with the
Penrose conditions (`IsPinv`), and `r` is Eq. 15 at `p = q = 2`, `‖·‖₂` written `√(β ⬝ᵥ β)`.

As in the proof: `H⁺x` solves `Hβ = x` (`HH⁺H = H`, `H` onto) and is orthogonal to `ker H`
(`H⁺ = H⁺HH⁺`, `H⁺H` symmetric), so it is the solution of least norm, and
`r² = max_{αᵀα ≤ 1} ‖Θα + θ‖²`, attained on the compact ball. The theorem of alternatives the
proof cites is the S-lemma at `g α = αᵀα - 1`, which `α = 0` makes strictly negative:
`s_lemma_posSemidef` turns `αᵀα ≤ 1 → ‖Θα + θ‖² ≤ ρ` into Eq. 23, so `S = [r², ∞)`.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- For `H` onto, `H⁺x` solves `Hβ = x` with the least `βᵀβ`. -/
theorem aux_pinv_least (H : Mat ℝ n l) (hH : Function.Surjective H.mulVec) (Hp : Mat ℝ l n)
    (hHp : IsPinv H Hp) (x : Fin n → ℝ) :
    H *ᵥ (Hp *ᵥ x) = x ∧
      ∀ β, H *ᵥ β = x → (Hp *ᵥ x) ⬝ᵥ (Hp *ᵥ x) ≤ β ⬝ᵥ β := by -- --- PROOF ---
  obtain ⟨h1, h2, -, h4⟩ := hHp
  have hsol : H *ᵥ (Hp *ᵥ x) = x := by
    obtain ⟨β, rfl⟩ := hH x
    rw [mulVec_mulVec, mulVec_mulVec, h1]
  refine ⟨hsol, fun β hβ => ?_⟩
  -- `w = β - H⁺x` lies in `ker H`, and `H⁺x = (H⁺H) H⁺x` is orthogonal to it
  set β₀ := Hp *ᵥ x
  have hw : H *ᵥ (β - β₀) = 0 := by rw [mulVec_sub, hβ, hsol, sub_self]
  set w := β - β₀ with hwdef
  have horth : β₀ ⬝ᵥ w = 0 := by
    have : β₀ = (Hp * H) *ᵥ β₀ := by
      rw [mulVec_mulVec, h2]
    rw [this, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h4, ← mulVec_mulVec, hw,
      mulVec_zero, zero_dotProduct]
  have hsq : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have : β ⬝ᵥ β = β₀ ⬝ᵥ β₀ + 2 * (β₀ ⬝ᵥ w) + w ⬝ᵥ w := by
    simp only [hwdef, dotProduct_sub, sub_dotProduct, dotProduct_comm β β₀]
    ring
  rw [this, horth]
  linarith

/-- The unit ball `αᵀα ≤ 1` is compact. -/
theorem aux_isCompact_ball : IsCompact {α : Fin m → ℝ | α ⬝ᵥ α ≤ 1} := by -- --- PROOF ---
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_id.dotProduct continuous_id) continuous_const)
    (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1) |>.subset fun α hα => ?_)
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have : α i * α i ≤ α ⬝ᵥ α :=
    Finset.single_le_sum (f := fun j => α j * α j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hle : α i * α i ≤ 1 := this.trans hα
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- The form of the S-lemma's `f` at `A = -ΘᵀΘ`, `a = -Θᵀθ`, `α = ρ - θᵀθ` is `ρ - ‖Θα + θ‖²`. -/
theorem aux_form_eq (Θ : Mat ℝ l m) (θ : Fin l → ℝ) (ρ : ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (-(Θᵀ * Θ)) *ᵥ x + 2 * (-(Θᵀ *ᵥ θ) ⬝ᵥ x) + (ρ - θ ⬝ᵥ θ) =
      ρ - (Θ *ᵥ x + θ) ⬝ᵥ (Θ *ᵥ x + θ) := by
  rw [neg_mulVec, dotProduct_neg, neg_dotProduct, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, mulVec_transpose, ← dotProduct_mulVec]
  simp only [dotProduct_add, add_dotProduct, dotProduct_comm θ (Θ *ᵥ x)]
  ring

/-- Eq. 23's matrix is the certificate of `s_lemma_posSemidef` for `f` and `αᵀα - 1`. -/
theorem aux_lmi_eq (Θ : Mat ℝ l m) (θ : Fin l → ℝ) (ρ δ : ℝ) : -- --- STMT ---
    δ • fromBlocks (1 : Mat ℝ m m) 0 0 (-1 : Mat ℝ 1 1) -
        (fromBlocks (Θᵀ * Θ) (replicateCol (Fin 1) (Θᵀ *ᵥ θ)) (replicateRow (Fin 1) (θ ᵥ* Θ))
          (of fun _ _ => θ ⬝ᵥ θ) - ρ • fromBlocks (0 : Mat ℝ m m) 0 0 (1 : Mat ℝ 1 1)) =
      fromBlocks (-(Θᵀ * Θ)) (replicateCol (Fin 1) (-(Θᵀ *ᵥ θ)))
          (replicateRow (Fin 1) (-(Θᵀ *ᵥ θ))) (of fun _ _ => ρ - θ ⬝ᵥ θ)
        + δ • fromBlocks (1 : Mat ℝ m m) (replicateCol (Fin 1) 0) (replicateRow (Fin 1) 0)
          (of fun _ _ => -1) := by -- --- PROOF ---
  ext (i | i) (j | j) <;>
    simp [fromBlocks, replicateCol, replicateRow, Fin.fin_one_eq_zero, mulVec_transpose] <;>
    ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 13]: `r(Ê, E)² = min S`, `S = [r², ∞)` the `ρ` with Eq. 23 for some `δ ≥ 0`. -/
theorem ellipsoid_containmentRadius_sdp (G : Mat ℝ n m) (c : Fin n → ℝ) (H : Mat ℝ n l)
    (d : Fin n → ℝ) (hH : Function.Surjective H.mulVec) (Hp : Mat ℝ l n)
    (hHp : IsPinv H Hp) : -- --- STMT ---
    let Θ := Hp * G
    let θ := Hp *ᵥ (c - d)
    let S := {ρ : ℝ | ∃ δ : ℝ, 0 ≤ δ ∧
      (δ • fromBlocks (1 : Mat ℝ m m) 0 0 (-1 : Mat ℝ 1 1) -
        (fromBlocks (Θᵀ * Θ) (replicateCol (Fin 1) (Θᵀ *ᵥ θ)) (replicateRow (Fin 1) (θ ᵥ* Θ))
          (of fun _ _ => θ ⬝ᵥ θ) - ρ • fromBlocks (0 : Mat ℝ m m) 0 0 (1 : Mat ℝ 1 1))).PosSemidef}
    ∃ ρ, IsLeast S ρ ∧ S = Set.Ici ρ ∧
      (∀ α : Fin m → ℝ, α ⬝ᵥ α ≤ 1 → ∃ β, H *ᵥ β = G *ᵥ α + c - d ∧ √(β ⬝ᵥ β) ≤ √ρ) ∧
      ∃ α : Fin m → ℝ, α ⬝ᵥ α ≤ 1 ∧
        ∀ β, H *ᵥ β = G *ᵥ α + c - d → √ρ ≤ √(β ⬝ᵥ β) := by -- --- PROOF ---
  intro Θ θ S
  have hF : ∀ α, Hp *ᵥ (G *ᵥ α + c - d) = Θ *ᵥ α + θ := fun α => by
    rw [add_sub_assoc, mulVec_add, mulVec_mulVec]
  -- the maximum of `‖Θα + θ‖²` over the ball
  have hcont : Continuous fun α : Fin m → ℝ => (Θ *ᵥ α + θ) ⬝ᵥ (Θ *ᵥ α + θ) := by
    have : Continuous fun α : Fin m → ℝ => Θ *ᵥ α + θ :=
      (continuous_const.matrix_mulVec continuous_id).add continuous_const
    exact this.dotProduct this
  obtain ⟨α₀, hα₀, hmax⟩ := aux_isCompact_ball.exists_isMaxOn
    ⟨0, by simp⟩ hcont.continuousOn
  set R := (Θ *ᵥ α₀ + θ) ⬝ᵥ (Θ *ᵥ α₀ + θ) with hR
  -- `S` is `[R, ∞)`, by the S-lemma at `g α = αᵀα - 1`
  have hS : ∀ ρ, ρ ∈ S ↔ ∀ α : Fin m → ℝ, α ⬝ᵥ α ≤ 1 → (Θ *ᵥ α + θ) ⬝ᵥ (Θ *ᵥ α + θ) ≤ ρ := by
    intro ρ
    have hsym : (-(Θᵀ * Θ)).IsSymm := IsSymm.neg (by simp [Matrix.IsSymm, transpose_mul])
    have key := s_lemma_posSemidef (-(Θᵀ * Θ)) 1 hsym isSymm_one (-(Θᵀ *ᵥ θ)) 0 (ρ - θ ⬝ᵥ θ) (-1)
      ⟨0, by simp⟩
    simp only [S, Set.mem_setOf_eq, aux_lmi_eq]
    rw [← key]
    refine forall_congr' fun α => ?_
    rw [aux_form_eq, one_mulVec, zero_dotProduct, mul_zero, add_zero]
    constructor
    · intro h hα; have := h (by linarith); linarith
    · intro h hα; have := h (by linarith); linarith
  have hRS : S = Set.Ici R := Set.ext fun ρ =>
    (hS ρ).trans ⟨fun h => h α₀ hα₀, fun h α hα => (hmax hα).trans h⟩
  refine ⟨R, hRS ▸ isLeast_Ici, hRS, fun α hα => ?_, α₀, hα₀, fun β hβ => ?_⟩
  · -- `H⁺(Gα + c - d)` is a solution of norm at most `√R`
    refine ⟨Hp *ᵥ (G *ᵥ α + c - d), (aux_pinv_least H hH Hp hHp _).1, ?_⟩
    rw [hF]
    exact Real.sqrt_le_sqrt (hmax hα)
  · -- at the maximizer every solution has norm at least `√R`
    have := (aux_pinv_least H hH Hp hHp _).2 β hβ
    rw [hF] at this
    exact Real.sqrt_le_sqrt this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
