module

public import CORALean.ContDynamics.Conform.Theorems.MemZcpSetIff
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A class is predicted iff a coefficient vector scores it highest

The equivalence chain in the proof of [1, Thm. 7]: for one-hot `e_c` (22), `classes(e_c) = {c}`,
and `{c} ⊆ classes(Y_ZCP(x))` iff some `z ∈ Y_ZCP(x)` has its `c`-th score largest, iff
`0 ≤ T z` for `T` of (21), iff by [1, Lemma 5] some `|β| ≤ α` has
`-T f(x) ≤ T D̄(x) G_u β` (20e). For `α ≥ 0`.

## Inputs
* `c` – class index
* `fx` – prediction at the point
* `D` – derivative in the uncertainties
* `Gu` – uncertainty generators
* `α` – generator scaling

## Hypotheses
* `hα` – scalings nonnegative

## Conclusion
* the class is predicted iff some coefficient vector fulfils the class constraints

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(T z)ᵢ = z_c - zᵢ`. -/
theorem aux_classMat_mulVec (c : Fin ny) (z : Vec ℝ ny) (i : Fin ny) :
    (Conform.classMat c *ᵥ z) i = z c - z i := by
  simp [Conform.classMat, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- `classes(e_c) = {c}`. -/
theorem aux_classesVec_single (c : Fin ny) : -- --- CONCL ---
    Conform.classesVec (Pi.single c 1 : Vec ℝ ny) = {c} := by -- --- PROOF ---
  ext i
  simp only [Conform.classesVec, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hic
    have := h c
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hic] at this
    linarith
  · rintro rfl j
    by_cases hj : j = i <;> simp [hj]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 7], (12b) at one point: `classes(e_c) ⊆ classes(Y_ZCP(x))` iff (20c)-(20e) have a
solution `β`. -/
theorem Conform.classesVec_single_subset_iff (c : Fin ny) (fx : Vec ℝ ny) (D : Mat ℝ ny nu)
    (Gu : ι → Vec ℝ nu) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) : -- --- CONCL ---
    Conform.classesVec (Pi.single c 1 : Vec ℝ ny)
        ⊆ Conform.classesSet (Conform.zcpSet fx D Gu α) ↔
      ∃ β : ι → ℝ, (∀ j, |β j| ≤ α j) ∧
        -(Conform.classMat c *ᵥ fx)
          ≤ Conform.classMat c *ᵥ ∑ j, β j • D *ᵥ Gu j := by -- --- PROOF ---
  rw [aux_classesVec_single, Set.singleton_subset_iff]
  simp only [Conform.classesSet, Set.mem_setOf_eq]
  constructor
  · -- the best-scoring point of the set, by (18)
    rintro ⟨z, hz, hmax⟩
    obtain ⟨β, hβ, rfl⟩ := (Conform.mem_zcpSet_iff _ _ _ _ hα _).mp hz
    refine ⟨β, hβ, fun i => ?_⟩
    have h := hmax i
    simp only [Pi.neg_apply, aux_classMat_mulVec, Pi.add_apply] at h ⊢
    linarith
  · -- and back: the point `f(x) + D̄ G_u β`
    rintro ⟨β, hβ, h₃⟩
    refine ⟨fx + ∑ j, β j • D *ᵥ Gu j,
      (Conform.mem_zcpSet_iff _ _ _ _ hα _).mpr ⟨β, hβ, rfl⟩, fun i => ?_⟩
    have h := h₃ i
    simp only [Pi.neg_apply, aux_classMat_mulVec, Pi.add_apply] at h ⊢
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
