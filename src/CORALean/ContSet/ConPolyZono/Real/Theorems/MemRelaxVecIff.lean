module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxIff
public import CORALean.Global.Entrywise

@[expose] public section

/-!
# What `ConPolyZono.relax` denotes, coordinatewise

`mem_relax_iff` at `Vec ℝ n`, the defining equation read one coordinate at a time with both
generator blocks transposed, as `mem_construct_iff` reads `construct`: the form a float layer's
enclosure proofs read the nominal half of a point in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mem_relax_iff` with the defining equation read one coordinate at a time. -/
theorem ConPolyZono.mem_relax_vec_iff (cPZ : ConPolyZono (Vec ℝ n)) (s : Vec ℝ cPZ.cons.m)
    {x : Vec ℝ n} : -- --- STMT ---
    x ∈ (cPZ.relax s).construct ↔
      ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ (∀ i, |(cPZ.cons.A *ᵥ PolyZonotope.monomial cPZ.cons.R a) i - cPZ.cons.b i| ≤ |s i|)
        ∧ ∀ i, x i = cPZ.c i + (∑ l, cPZ.G l i * PolyZonotope.monomial cPZ.E a l)
              + ∑ j, cPZ.GI j i * β j := by -- --- PROOF ---
  -- one coordinate of the defining equation, both generator blocks transposed
  have key : ∀ (a : Fin cPZ.p → ℝ) (β : Fin cPZ.qI → ℝ) (i : Fin n),
      (cPZ.c + ∑ l, PolyZonotope.monomial cPZ.E a l • cPZ.G l + ∑ j, β j • cPZ.GI j) i
        = cPZ.c i + (∑ l, cPZ.G l i * PolyZonotope.monomial cPZ.E a l)
            + ∑ j, cPZ.GI j i * β j := by
    intro a β i
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  rw [ConPolyZono.mem_relax_iff]
  constructor
  · rintro ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, key a β⟩
  · rintro ⟨a, β, ha, hβ, hsat, hx⟩
    exact ⟨a, β, ha, hβ, hsat, funext fun i => (hx i).trans (key a β i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
