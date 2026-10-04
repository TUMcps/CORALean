import CORALean.ContSet.ConPolyZono.Real.Operations.ExtPolyZonotope
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi

/-!
# The extended point is in the extended polynomial zonotope iff the constraint reads `A μ = b + t`

`[p; t] ∈ extPolyZonotope` iff some factors in the unit box and independent factors give `p` by the
generators and `A μ(α) = b + t` by the constraint rows. The generators' sum splits into the two
blocks of `extPolyZonotope`, the monomials of `appendE` being those of either half.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The extended generators' sum splits into the two blocks. -/
theorem ConPolyZono.aux_sum_ext (cPZ : ConPolyZono (Vec ℝ n)) (a : Fin cPZ.p → ℝ) :
    ∑ i : Fin cPZ.extPolyZonotope.h,
        PolyZonotope.monomial cPZ.extPolyZonotope.E a i • cPZ.extPolyZonotope.G i
      = (∑ i : Fin cPZ.h, PolyZonotope.monomial cPZ.E a i • ((cPZ.G i, 0) : Vec ℝ n × Vec ℝ cPZ.m))
        + ∑ l : Fin cPZ.s, PolyZonotope.monomial cPZ.EC a l
            • ((0, ConPolyZono.consCol cPZ.A l) : Vec ℝ n × Vec ℝ cPZ.m) := by -- --- PROOF ---
  show ∑ i : Fin (cPZ.h + cPZ.s), PolyZonotope.monomial (ConPolyZono.appendE cPZ.E cPZ.EC) a i
      • (Fin.append (fun i => ((cPZ.G i, 0) : Vec ℝ n × Vec ℝ cPZ.m))
          (fun l => ((0, ConPolyZono.consCol cPZ.A l) : Vec ℝ n × Vec ℝ cPZ.m)) i) = _
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.monomial_appendE_left, ConPolyZono.monomial_appendE_right,
    Fin.append_left, Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_extPolyZonotope_iff (cPZ : ConPolyZono (Vec ℝ n)) (p : Vec ℝ n)
    (t : Vec ℝ cPZ.m) :
    (p, t) ∈ cPZ.extPolyZonotope.construct ↔
      ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ (∀ i, (cPZ.A *ᵥ PolyZonotope.monomial cPZ.EC a) i = cPZ.b.inf i + t i)
        ∧ p = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i
            + ∑ j, β j • cPZ.GI j := by -- --- PROOF ---
  constructor
  · -- the two components of the stacked equation: the constraint rows, then the generators
    rintro ⟨a, β, ha, hβ, hx⟩
    rw [ConPolyZono.aux_sum_ext] at hx
    refine ⟨a, β, ha, hβ, fun i => ?_, ?_⟩
    · have := congrFun (congrArg Prod.snd hx) i
      simp [ConPolyZono.extPolyZonotope, Prod.snd_sum, Finset.sum_apply, Matrix.mulVec,
        dotProduct, ConPolyZono.consCol, PolyZonotope.monomial, mul_comm] at this ⊢
      linarith
    · have := congrArg Prod.fst hx
      simp [ConPolyZono.extPolyZonotope, Prod.fst_sum] at this
      exact this
  · -- and the two components assemble the stacked equation
    rintro ⟨a, β, ha, hβ, hc, hx⟩
    refine ⟨a, β, ha, hβ, ?_⟩
    rw [ConPolyZono.aux_sum_ext]
    refine Prod.ext ?_ ?_
    · simp [ConPolyZono.extPolyZonotope, Prod.fst_sum]
      exact hx
    · funext i
      have := hc i
      simp [ConPolyZono.extPolyZonotope, Prod.snd_sum, Finset.sum_apply, Matrix.mulVec,
        dotProduct, ConPolyZono.consCol, PolyZonotope.monomial, mul_comm] at this ⊢
      linarith


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
