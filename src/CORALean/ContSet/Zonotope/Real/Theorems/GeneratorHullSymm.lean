import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEqConstruct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A zonotope of the evolution is centrally symmetric

[1, Sec. 3 (centre)]: the zonotope `Z(s; g₁, …, g_m)` is centrally symmetric about `s + ½ ∑ gᵢ`
("the operation ⊕ preserves central symmetry"): a point `y` is in it iff its reflection
`2c − y` is. About the centre the coefficients of `y` are `β`, and those of `2c − y` are `−β`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (centre)]: `y ∈ Z(s; g)` iff `2c − y ∈ Z(s; g)` for the centre `c = s + ½ ∑ gᵢ`. -/
theorem Zonotope.generatorHull_symm (s : Vec ℝ n) (m : ℕ) (g : Fin m → Vec ℝ n)
    (y : Vec ℝ n) : y ∈ Zonotope.generatorHull s m g ↔
      (2 : ℝ) • (s + (1 / 2 : ℝ) • ∑ i, g i) - y
        ∈ Zonotope.generatorHull s m g := by -- --- PROOF ---
  rw [Zonotope.generatorHull_eq_construct]
  set c : Vec ℝ n := s + (1 / 2 : ℝ) • ∑ i, g i with hc
  -- reflecting through `c` negates every coefficient, in either direction
  have key : ∀ y : Vec ℝ n, y ∈ (Zonotope.mk m c (fun i => (1 / 2 : ℝ) • g i)).construct →
      (2 : ℝ) • c - y ∈ (Zonotope.mk m c (fun i => (1 / 2 : ℝ) • g i)).construct := by
    rintro y ⟨β, hβ, rfl⟩
    refine ⟨fun i => -β i, fun i => by simpa using hβ i, ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]
    rw [two_smul]
    abel
  refine ⟨key y, fun h => ?_⟩
  have := key _ h
  rwa [sub_sub_cancel] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
