module

public import CORALean.ContSet.ConZonotope.Real.Operations.Rescale
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `ConZonotope.rescale` changes the representation, not the set

[1, Prop. 4]: if `B∞(A, b) ⊂ [ξL, ξU] ⊂ [-1, 1]` then `Z = {G diag(ξr), c + G ξm, A diag(ξr),
b − A ξm}`. `B∞(A, b)` is the set of `ξ` with `‖ξ‖∞ ≤ 1` and `Aξ = b`, and `Z` is `ofMat c G A b`.

`[ξL, ξU] ⊂ [-1, 1]` is read as both endpoint vectors lying in `[-1, 1]`, the form the proof
uses: `ξm + diag(ξr) δ` is then a convex combination of the endpoints, whatever their order.
Read as a set inclusion it also admits an empty interval with endpoints outside `[-1, 1]`,
where the statement fails.

## Inputs
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `ξL` – lower coefficient bounds
* `ξU` – upper coefficient bounds

## Hypotheses
* `hB` – the bounds enclose every feasible coefficient vector
* `hL` – lower bounds lie in the unit interval
* `hU` – upper bounds lie in the unit interval

## Conclusion
* rescaling leaves the set unchanged

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A diag(ξr) δ` is `A` applied to the entrywise product `ξr ∘ δ`. -/
private theorem ConZonotope.aux_mulVec_diagonal {q h : ℕ} (A : Mat ℝ q h) (ξr δ : Vec ℝ h) :
    (A * Matrix.diagonal ξr) *ᵥ δ = A *ᵥ fun j => ξr j * δ j := by
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext j
  simp [Matrix.mulVec_diagonal]

/-- Whatever the order of the endpoints, `ξm + ξr δ` is a convex combination of them. -/
private theorem ConZonotope.aux_abs_midpoint_le {a u δ : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1)
    (hδ : |δ| ≤ 1) : -- --- CONCL ---
    |(u + a) / 2 + (u - a) / 2 * δ| ≤ 1 := by -- --- PROOF ---
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  obtain ⟨hδ1, hδ2⟩ := abs_le.mp hδ
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hδ1),
      mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hδ2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hu2) (sub_nonneg.2 hδ1),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hδ2)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4]: `{G, c, A, b} = {G diag(ξr), c + G ξm, A diag(ξr), b − A ξm}` once the
coefficient box `[ξL, ξU]` contains `B∞(A, b)` and has its endpoints in `[-1, 1]`. -/
theorem ConZonotope.rescale_exact {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h)
    (b : Vec ℝ q) (ξL ξU : Vec ℝ h)
    (hB : ∀ ξ : Vec ℝ h, (∀ j, |ξ j| ≤ 1) → A *ᵥ ξ = b → ∀ j, ξL j ≤ ξ j ∧ ξ j ≤ ξU j)
    (hL : ∀ j, |ξL j| ≤ 1) (hU : ∀ j, |ξU j| ≤ 1) : -- --- CONCL ---
    (ConZonotope.ofMat c G A b).construct
      = (ConZonotope.rescale c G A b ξL ξU).construct := by -- --- PROOF ---
  ext x
  unfold ConZonotope.rescale
  simp only [ConZonotope.mem_ofMat_iff]
  -- the sum of a coefficient vector `ξm + ξr ∘ δ`, split into its two parts
  have hsum : ∀ δ : Vec ℝ h, ∑ j, ((ξU j + ξL j) / 2 + (ξU j - ξL j) / 2 * δ j) • G j
      = ∑ j, ((ξU j + ξL j) / 2) • G j + ∑ j, δ j • ((ξU j - ξL j) / 2) • G j := by
    intro δ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_smul, smul_smul, mul_comm]
  constructor
  · rintro ⟨β, hβ, hAβ, rfl⟩
    have hbd := hB β hβ (funext hAβ)
    -- δ = (β − ξm)/ξr, or 0 where the interval is a point
    set δ : Vec ℝ h := fun j =>
      if ξU j - ξL j = 0 then 0 else (β j - (ξU j + ξL j) / 2) / ((ξU j - ξL j) / 2) with hδ
    have hkey : ∀ j, β j = (ξU j + ξL j) / 2 + (ξU j - ξL j) / 2 * δ j := by
      intro j
      by_cases h0 : ξU j - ξL j = 0
      · simp only [hδ, h0, if_true]
        linarith [hbd j]
      · simp only [hδ, h0, if_false]
        field_simp
        ring
    refine ⟨δ, fun j => ?_, fun i => ?_, ?_⟩
    · by_cases h0 : ξU j - ξL j = 0
      · simp [hδ, h0]
      · have hnn : 0 ≤ ξU j - ξL j := by linarith [hbd j]
        have hpos : 0 < (ξU j - ξL j) / 2 := by linarith [lt_of_le_of_ne hnn (Ne.symm h0)]
        simp only [hδ, h0, if_false]
        rw [abs_le, le_div_iff₀ hpos, div_le_iff₀ hpos]
        constructor <;> linarith [hbd j]
    · -- (A diag ξr) δ = A (β − ξm) = b − A ξm
      rw [ConZonotope.aux_mulVec_diagonal]
      have hβm : (fun j => (ξU j - ξL j) / 2 * δ j) = fun j => β j - (ξU j + ξL j) / 2 := by
        funext j; linarith [hkey j]
      have hAm : A *ᵥ (fun j => β j - (ξU j + ξL j) / 2)
          = b - A *ᵥ fun j => (ξU j + ξL j) / 2 := by
        rw [show (fun j => β j - (ξU j + ξL j) / 2) = β - fun j => (ξU j + ξL j) / 2 from rfl,
          Matrix.mulVec_sub, funext hAβ]
      rw [hβm]
      exact congrFun hAm i
    · -- the value, `β = ξm + ξr ∘ δ` split into its two sums
      have hβG : ∑ j, β j • G j
          = ∑ j, ((ξU j + ξL j) / 2 + (ξU j - ξL j) / 2 * δ j) • G j :=
        Finset.sum_congr rfl fun j _ => by rw [← hkey j]
      rw [hβG, hsum δ]
      abel
  · rintro ⟨δ, hδ, hAδ, hx⟩
    rw [ConZonotope.aux_mulVec_diagonal] at hAδ
    refine ⟨fun j => (ξU j + ξL j) / 2 + (ξU j - ξL j) / 2 * δ j,
      fun j => ConZonotope.aux_abs_midpoint_le (hL j) (hU j) (hδ j), fun i => ?_, ?_⟩
    · -- A (ξm + ξr ∘ δ) = A ξm + (b − A ξm)
      have hsplit : (fun j => (ξU j + ξL j) / 2 + (ξU j - ξL j) / 2 * δ j)
          = (fun j => (ξU j + ξL j) / 2) + fun j => (ξU j - ξL j) / 2 * δ j := rfl
      rw [hsplit, Matrix.mulVec_add]
      have := hAδ i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      linarith
    · rw [hx, hsum δ]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
