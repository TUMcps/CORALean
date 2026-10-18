module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff
public import CORALean.ContSet.HPolytope.Float.Definitions.Basic

@[expose] public section

/-!
# Membership in the nominal part of a float polytope without slack

Where both slacks read `0`, every inequality is read at its stored `b` and every slab closes to
its hyperplane, so membership is the stored rows read exactly: the form every constructor's
result, and every result that carries no slack, is read in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With both slacks reading `0`, the nominal part is the stored rows read exactly. -/
theorem HPolytope.mem_nominal_iff_exact {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.IsSlackFree) {x : Vec ℝ n} : -- --- STMT ---
    x ∈ P.nominal.construct ↔
      (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
        ∧ ∀ i, (toRealMat P.Ae *ᵥ x) i = toReal (P.be i) := by -- --- PROOF ---
  rw [HPolytope.mem_nominal_iff]
  -- the slacks read `0`, so each slab is its hyperplane
  simp only [h.1, h.2, abs_zero, add_zero, abs_nonpos_iff, sub_eq_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
