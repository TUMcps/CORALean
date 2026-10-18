module

public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.Slab

@[expose] public section

/-!
# Membership in the nominal part of `HPolytope.slab`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_slab_nominal_iff {A : Mat 𝕋 q n} {lo hi : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab A lo hi).nominal.construct ↔
      ∀ i, toReal (lo i) ≤ (toRealMat A *ᵥ x) i
        ∧ (toRealMat A *ᵥ x) i ≤ toReal (hi i) := by -- --- PROOF ---
  unfold HPolytope.slab
  rw [HPolytope.mem_stackRows_nominal_iff, HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.ineqs, toRealMat_neg_mulVec, Pi.neg_apply, toReal_neg', toReal_zero,
    abs_zero, add_zero]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, -⟩ i
    exact ⟨by linarith [h2 i], h1 i⟩
  · intro h
    exact ⟨⟨fun i => (h i).2, fun i => i.elim0⟩, fun i => by linarith [(h i).1], fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
