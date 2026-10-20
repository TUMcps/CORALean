module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEq
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A zonotope of the evolution, about its center

[1, Sec. 3 (center)]: the center of `Z(s; g₁, …, g_m)` is `s + ½ ∑ gᵢ`, and about it the zonotope is
the symmetric box of the halved generators, `{c + ∑ βᵢ (gᵢ/2) | β ∈ [−1, 1]^m}`: the coefficient
`αᵢ ∈ [0, 1]` of `gᵢ` is `(1 + βᵢ)/2`. So the evolution is a zonotope in the sense of
`Zonotope.construct`, with center `c` and generators `gᵢ/2`.

## Inputs
* `s` – starting point
* `m` – generator count
* `g` – generators

## Hypotheses
* none

## Conclusion
* the hull is a zonotope with shifted center and halved generators

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (center)]: `{s} ⊕ g₁ ⊕ ⋯ ⊕ g_m` has center `s + ½ ∑ gᵢ`, generators `gᵢ/2`. -/
theorem Zonotope.generatorHull_eq_construct (s : Vec ℝ n) (m : ℕ) (g : Fin m → Vec ℝ n) :
    Zonotope.generatorHull s m g
      = (Zonotope.mk m (s + (1 / 2 : ℝ) • ∑ i, g i)
          (fun i => (1 / 2 : ℝ) • g i)).construct := by -- --- PROOF ---
  rw [Zonotope.generatorHull_eq]
  ext y
  simp only [Set.mem_setOf_eq, Zonotope.construct]
  constructor
  · -- `αᵢ ↦ 2αᵢ − 1`
    rintro ⟨α, hα, rfl⟩
    refine ⟨fun i => 2 * α i - 1, fun i => ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith [(hα i).1, (hα i).2]
    · simp only [smul_smul, Finset.smul_sum, add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← add_smul]
      congr 1
      ring
  · -- `βᵢ ↦ (1 + βᵢ)/2`
    rintro ⟨β, hβ, rfl⟩
    refine ⟨fun i => (1 + β i) / 2, fun i => ?_, ?_⟩
    · have := abs_le.1 (hβ i)
      constructor <;> linarith [this.1, this.2]
    · simp only [smul_smul, Finset.smul_sum, add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← add_smul]
      congr 1
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
