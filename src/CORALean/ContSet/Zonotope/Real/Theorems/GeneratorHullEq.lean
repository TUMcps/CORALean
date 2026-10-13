module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Definitions.GeneratorHull
public import CORALean.ContSet.Zonotope.Real.Theorems.SegmentSumEq
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A zonotope of the evolution, parametrized by the unit cube

[1, Def. 1.3]: `{s} ⊕ g₁ ⊕ ⋯ ⊕ g_m = {s + ∑ αᵢ gᵢ | α ∈ [0, 1]^m}`, by induction on `m`. The hull
so far is convex, being the image of a cube, so [1, Eq. 12] applies at each step; and a
coefficient vector in `[0, 1]^{m+1}` is one in `[0, 1]^m` and a last coefficient in `[0, 1]`.

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

/-- [1, Def. 1.3]: `{s} ⊕ g₁ ⊕ ⋯ ⊕ g_m` is the set of `s + ∑ αᵢ gᵢ`, `α ∈ [0, 1]^m`. -/
theorem Zonotope.generatorHull_eq (s : Vec ℝ n) :
    ∀ (m : ℕ) (g : Fin m → Vec ℝ n), Zonotope.generatorHull s m g
      = {y | ∃ α : Fin m → ℝ, (∀ i, α i ∈ Set.Icc (0:ℝ) 1) ∧ y = s + ∑ i, α i • g i}
  | 0, g => by
      ext y
      simp [Zonotope.generatorHull]
  | m + 1, g => by
      have ih := Zonotope.generatorHull_eq s m (Fin.init g)
      -- the hull so far is convex, being the image of a cube
      have hc : Convex ℝ (Zonotope.generatorHull s m (Fin.init g)) := by -- --- PROOF ---
        rw [ih]
        rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ p q hp hq hpq
        refine ⟨fun i => p * α i + q * β i, fun i => ⟨?_, ?_⟩, ?_⟩
        · nlinarith [(hα i).1, (hβ i).1]
        · nlinarith [(hα i).2, (hβ i).2]
        · simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
          have hs : p • s + q • s = s := by rw [← add_smul, hpq, one_smul]
          rw [add_add_add_comm, hs]
      rw [Zonotope.generatorHull, Zonotope.segmentSum_eq hc]
      ext y
      simp only [Set.mem_setOf_eq, ih]
      constructor
      · -- extend the coefficients by the last one, `t ∈ [0, 1]`
        rintro ⟨_, ⟨α, hα, rfl⟩, t, ht, rfl⟩
        refine ⟨Fin.snoc (α := fun _ => ℝ) α t, fun i => ?_, ?_⟩
        · refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using ht
          · simpa using hα j
        · rw [Fin.sum_univ_castSucc]
          simp [add_assoc]
          rfl
      · -- and split them again
        rintro ⟨α, hα, rfl⟩
        refine ⟨_, ⟨fun i => α (Fin.castSucc i), fun i => hα _, rfl⟩, α (Fin.last m), hα _, ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp [add_assoc, Fin.init]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
