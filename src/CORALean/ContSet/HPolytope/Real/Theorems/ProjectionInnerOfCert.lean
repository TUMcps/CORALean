module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An inner approximation of a projection, with a Hausdorff bound

`[1, Prop. 7]`: for `F = {(x, u) | H x + F u ≤ g}` and its projection `F_proj`, a feasible
point of `[1, Prop. 7, Eq. 45]` makes `X = x̄ + {Hₓ x ≤ 1}` an inner approximation of `F_proj`
within `ε` of it (`F_proj ⊆ X ⊕ ε P_Ball`). As printed the program is wrong: `Λ₂ g` is
bounded by `ε h_Ball - H_Ball x̄ + H_Ball βₓ`, which `[1, Thm. 1]` applied to
`F_proj ⊆ x̄ + X₀ ⊕ ε P_Ball` gives with `+ H_Ball x̄`; the printed sign certifies
`F_proj ⊆ -x̄ + X₀ ⊕ ε P_Ball` instead (`projection_inner_of_cert_counterexample`). Two
misprints are read the only way the dimensions allow: `H_B` is `H_Ball`, and `h_Ball` in
`Λ₁ g ≤ h_Ball - Hₓ βₓ` is `1`, the right-hand side of `X₀`.

## Inputs
* `H` – `q × n` matrix
* `F` – `q × m` matrix
* `g` – vector of length `q`
* `Hx` – `r × n` matrix
* `xbar` – mean of length `n`
* `HB` – `qB × n` matrix
* `hB` – vector of length `qB`
* `ε` – tolerance
* `Λ₀` – `q × r` matrix
* `Λ₁` – `r × q` matrix
* `Λ₂` – `qB × q` matrix
* `Γ` – `m × n` matrix
* `βu` – vector of length `m`
* `X₁` – `n × n` matrix
* `X₂` – `n × m` matrix
* `βx` – vector of length `n`

## Hypotheses
* `hΛ₀` – `Λ₀` has nonnegative entries
* `hΛ₁` – `Λ₁` has nonnegative entries
* `hΛ₂` – `Λ₂` has nonnegative entries
* `e₀` – `Λ₀` carries `Hx` to `H + F Γ`
* `f₀` – the bound of `Λ₀` is at most `g` shifted by `-H xbar + F βu`
* `e₁` – `Λ₁` carries `H` to `Hx X₁`
* `e₂` – `Λ₁` carries `F` to `Hx X₂`
* `e₃` – `Λ₂` carries `H` to `HB - HB X₁`
* `e₄` – `Λ₂` carries `F` to `-HB X₂`
* `f₁` – the bound of `Λ₁` is at most `1 - Hx βx`
* `f₂` – the bound of `Λ₂` is at most `ε hB` shifted by `HB (xbar + βx)`

## Conclusion
* an inner approximation of a projection, with a Hausdorff bound

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC), 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n m q r qB : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.projection_inner_of_cert {H : Mat ℝ q n} {F : Mat ℝ q m} {g : Vec ℝ q}
    {Hx : Mat ℝ r n} {xbar : Vec ℝ n} {HB : Mat ℝ qB n} {hB : Vec ℝ qB} {ε : ℝ}
    {Λ₀ : Mat ℝ q r} {Λ₁ : Mat ℝ r q} {Λ₂ : Mat ℝ qB q} {Γ : Mat ℝ m n} {βu : Vec ℝ m}
    {X₁ : Mat ℝ n n} {X₂ : Mat ℝ n m} {βx : Vec ℝ n}
    (hΛ₀ : ∀ i j, 0 ≤ Λ₀ i j) (hΛ₁ : ∀ i j, 0 ≤ Λ₁ i j) (hΛ₂ : ∀ i j, 0 ≤ Λ₂ i j)
    (e₀ : Λ₀ * Hx = H + F * Γ) (f₀ : Λ₀ *ᵥ 1 ≤ g - H *ᵥ xbar + F *ᵥ βu)
    (e₁ : Λ₁ * H = Hx * X₁) (e₂ : Λ₁ * F = Hx * X₂) (e₃ : Λ₂ * H = HB - HB * X₁)
    (e₄ : Λ₂ * F = -(HB * X₂)) (f₁ : Λ₁ *ᵥ g ≤ 1 - Hx *ᵥ βx)
    (f₂ : Λ₂ *ᵥ g ≤ ε • hB + HB *ᵥ xbar + HB *ᵥ βx) : -- --- CONCL ---
    HPolytope.ahPolytope xbar 1 (HPolytope.ineqs Hx 1) ⊆ {x | ∃ u, H *ᵥ x + F *ᵥ u ≤ g} ∧
      {x | ∃ u, H *ᵥ x + F *ᵥ u ≤ g}
        ⊆ HPolytope.ahPolytope xbar 1 (HPolytope.ineqs Hx 1)
          + (HPolytope.ineqs HB (ε • hB)).construct := by -- --- PROOF ---
  -- a nonnegative matrix keeps an inequality between vectors
  have mono : ∀ {a b : ℕ} (M : Mat ℝ a b), (∀ i j, 0 ≤ M i j) → ∀ v w : Vec ℝ b, v ≤ w →
      M *ᵥ v ≤ M *ᵥ w := fun M hM v w hvw i => by
    simp only [mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j) (hM i j)
  constructor
  -- `x̄ + z ∈ F_proj` with `u = Γ z - βu`
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨Γ *ᵥ z - βu, fun i => ?_⟩
    have hz' : Hx *ᵥ z ≤ 1 := fun i => HPolytope.mem_ineqs_iff.mp hz i
    have h := mono Λ₀ hΛ₀ _ _ hz' i
    rw [mulVec_mulVec, e₀] at h
    have hf := f₀ i
    simp only [Pi.add_apply, Pi.sub_apply, add_mulVec, mulVec_add, mulVec_sub, mulVec_mulVec,
      one_mulVec] at h hf ⊢
    linarith
  -- `x = (x̄ + z₁) + z₂` with `z₁ = X₁ x + X₂ u + βx`
  · rintro x ⟨u, hu⟩
    refine Set.mem_add.mpr ⟨xbar + (X₁ *ᵥ x + X₂ *ᵥ u + βx),
      ⟨X₁ *ᵥ x + X₂ *ᵥ u + βx, HPolytope.mem_ineqs_iff.mpr fun i => ?_, by rw [one_mulVec]⟩,
      x - X₁ *ᵥ x - X₂ *ᵥ u - xbar - βx, HPolytope.mem_ineqs_iff.mpr fun i => ?_, by abel⟩
    · have h := mono Λ₁ hΛ₁ _ _ hu i
      have hf := f₁ i
      simp only [mulVec_add, mulVec_mulVec, e₁, e₂] at h
      simp only [mulVec_add, ← mulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.one_apply] at h hf ⊢
      linarith
    · have h := mono Λ₂ hΛ₂ _ _ hu i
      have hf := f₂ i
      simp only [mulVec_add, mulVec_mulVec, e₃, e₄] at h
      simp only [mulVec_sub, sub_mulVec, neg_mulVec, ← mulVec_mulVec, Pi.add_apply,
        Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h hf ⊢
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
