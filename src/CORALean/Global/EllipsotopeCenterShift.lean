module

public import CORALean.Global.CoeffNorm
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# A zonotope's center shift is one more generator

[1, Lemma 14]: for a zonotope inbody `Z(G, c)` and an ellipsotope circumbody `E_q(H, d)`,
`r(Z(G, c), E_q(H, d)) = r(Z(G'), E_q(H))` with `G' = [G, c - d]`, `r` the maximum of the
circumbody's norm over the inbody. The maximum over the `m + 1` coefficients of `G'` is the one
over `α` of `‖G α + γ (c - d)‖` at `γ ∈ [-1, 1]`: the norm is convex in `γ`, so `γ = ±1` (Bauer),
and `α ↦ -α` carries `γ = -1` to `γ = 1`. Stated as the two maxima being the same numbers, the
circumbody's norm being any `coeffNorm` of a surjective map.

## Inputs
* `G` – generator map of the inner zonotope
* `c` – center of the inner zonotope
* `d` – center of the outer ellipsotope
* `H` – generator map of the outer ellipsotope
* `r` – candidate radius

## Hypotheses
* `hH` – the outer generator map is onto

## Conclusion
* the radius is the maximum exactly when it is the one with the center difference as generator

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {m : ℕ} {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup W] [Module ℝ W]


-- =======================================  MAIN THEOREM  ======================================= --

theorem isGreatest_coeffNorm_center_shift (G : (Fin m → ℝ) →ₗ[ℝ] W) (c d : W)
    (H : E →ₗ[ℝ] W) (hH : Function.Surjective H) (r : ℝ) : -- --- CONCL ---
    IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1) r ↔
      IsGreatest ((fun α' : Fin (m + 1) → ℝ =>
        coeffNorm H (G (fun i => α' i.castSucc) + α' (Fin.last m) • (c - d))) ''
          Metric.closedBall 0 1) r := by -- --- PROOF ---
  -- the norm is even, and convex
  have hneg : ∀ x, coeffNorm H (-x) = coeffNorm H x := fun x => by
    simpa using coeffNorm_smul H (hH x) (-1)
  have hconv : ∀ (x v : W) (t : ℝ), |t| ≤ 1 →
      coeffNorm H (x + t • v) ≤ max (coeffNorm H (x + v)) (coeffNorm H (x - v)) := by
    intro x v t ht
    have ht' := abs_le.mp ht
    -- `x + t v` is the convex combination `(1+t)/2 (x + v) + (1-t)/2 (x - v)`
    have hcomb : x + t • v = ((1 + t) / 2) • (x + v) + ((1 - t) / 2) • (x - v) := by module
    rw [hcomb]
    refine (coeffNorm_add_le H (hH _) (hH _)).trans ?_
    rw [coeffNorm_smul H (hH _), coeffNorm_smul H (hH _),
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have h1 := le_max_left (coeffNorm H (x + v)) (coeffNorm H (x - v))
    have h2 := le_max_right (coeffNorm H (x + v)) (coeffNorm H (x - v))
    have h3 := coeffNorm_nonneg H (x + v)
    have h4 := coeffNorm_nonneg H (x - v)
    nlinarith
  -- the coefficient balls are the boxes
  have hball : ∀ {k : ℕ} (a : Fin k → ℝ), a ∈ Metric.closedBall (0 : Fin k → ℝ) 1 ↔
      ∀ i, |a i| ≤ 1 := fun a => by
    simp [pi_norm_le_iff_of_nonneg zero_le_one]
  -- the shifted-center value at `α` is the larger family's value at `(α, 1)`
  have hlift : ∀ α : Fin m → ℝ, (fun i => (Fin.snoc α 1 : Fin (m + 1) → ℝ) i.castSucc) = α ∧
      (Fin.snoc α 1 : Fin (m + 1) → ℝ) (Fin.last m) = 1 := fun α => by
    simp
  have hmem : ∀ α : Fin m → ℝ, (∀ i, |α i| ≤ 1) → ∀ i, |(Fin.snoc α 1 : Fin (m + 1) → ℝ) i| ≤ 1 :=
    fun α hα i => by
      refine Fin.lastCases (by simp) (fun i => ?_) i
      simpa using hα i
  -- every value of the larger family is at most a value of the shifted-center one
  have hbound : ∀ α' : Fin (m + 1) → ℝ, (∀ i, |α' i| ≤ 1) → ∃ β : Fin m → ℝ, (∀ i, |β i| ≤ 1) ∧
      coeffNorm H (G (fun i => α' i.castSucc) + α' (Fin.last m) • (c - d)) ≤
        coeffNorm H (G β + c - d) := by
    intro α' hα'
    set a : Fin m → ℝ := fun i => α' i.castSucc with ha
    have h1 := hconv (G a) (c - d) (α' (Fin.last m)) (hα' _)
    -- the minus corner is the plus corner at `-a`
    have h2 : coeffNorm H (G a - (c - d)) = coeffNorm H (G (-a) + c - d) := by
      rw [← hneg, map_neg]
      congr 1
      abel
    have h3 : coeffNorm H (G a + (c - d)) = coeffNorm H (G a + c - d) := by rw [add_sub_assoc]
    rw [h2, h3] at h1
    rcases le_total (coeffNorm H (G (-a) + c - d)) (coeffNorm H (G a + c - d)) with h | h
    · exact ⟨a, fun i => hα' _, h1.trans (max_le le_rfl h)⟩
    · exact ⟨-a, fun i => by simpa using hα' i.castSucc, h1.trans (max_le h le_rfl)⟩
  constructor
  · -- the shifted-center maximum is a maximum of the larger family
    rintro ⟨⟨α, hα, rfl⟩, hmax⟩
    have hα' := (hball α).mp hα
    refine ⟨⟨Fin.snoc α 1, (hball _).mpr (hmem α hα'), ?_⟩, ?_⟩
    · simp [add_sub_assoc]
    · rintro _ ⟨α', hα'', rfl⟩
      obtain ⟨β, hβ, hle⟩ := hbound α' ((hball α').mp hα'')
      exact hle.trans (hmax ⟨β, (hball β).mpr hβ, rfl⟩)
  · -- and a maximum of the larger family is attained at some `(α, 1)`
    rintro ⟨⟨α', hα', rfl⟩, hmax⟩
    obtain ⟨β, hβ, hle⟩ := hbound α' ((hball α').mp hα')
    have hβ' : coeffNorm H (G β + c - d) ≤ coeffNorm H
        (G (fun i => α' i.castSucc) + α' (Fin.last m) • (c - d)) := by
      refine hmax ⟨Fin.snoc β 1, (hball _).mpr (hmem β hβ), ?_⟩
      simp [add_sub_assoc]
    have heq := le_antisymm hle hβ'
    refine ⟨⟨β, (hball β).mpr hβ, heq.symm⟩, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    show coeffNorm H (G α + c - d) ≤ coeffNorm H
      ((G fun i => α' i.castSucc) + α' (Fin.last m) • (c - d))
    refine hmax ⟨Fin.snoc α 1, (hball _).mpr (hmem α ((hball α).mp hα)), ?_⟩
    simp [add_sub_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
