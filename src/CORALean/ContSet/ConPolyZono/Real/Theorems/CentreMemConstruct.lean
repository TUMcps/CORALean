module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Centre
public import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol

@[expose] public section

/-!
# A constrained polynomial zonotope with no zero exponent column contains its centre

CORA's `center` returns the field `c` with no guarantee. At the factor vector `0` every monomial
vanishes when no exponent column of `E` (and of `EC`) is zero, so the point is `c`; the constraint
`A μ(0) ∈ b` then reads `0 ∈ b`. Without these hypotheses `c` need not lie in the set: one
generator `1` with exponent column `0` denotes `{c + 1}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.centre_mem_construct (cPZ : ConPolyZono α)
    (hE : ConPolyZono.NoZeroCol cPZ.E) (hEC : ConPolyZono.NoZeroCol cPZ.EC)
    (h0 : ∀ i, cPZ.b.inf i ≤ 0 ∧ 0 ≤ cPZ.b.sup i) :
    cPZ.centre ∈ cPZ.construct := by -- --- PROOF ---
  refine ⟨fun _ => 0, fun _ => 0, fun k => by simp, fun j => by simp, ?_, ?_⟩
  · intro i
    have hm : PolyZonotope.monomial cPZ.EC (fun _ => (0 : ℝ)) = 0 :=
      funext fun j => ConPolyZono.monomial_eq_zero_of_noZeroCol hEC (fun _ => rfl) j
    simp only [hm, Matrix.mulVec_zero, Pi.zero_apply]
    exact h0 i
  · simp [ConPolyZono.centre, ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
