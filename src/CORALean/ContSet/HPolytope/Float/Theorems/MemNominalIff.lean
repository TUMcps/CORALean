module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Real.Theorems.MemSlabIff

@[expose] public section

/-!
# Membership in the nominal part of a float polytope

The nominal part is the exact layer's `ineqs` at `b + |b_error|` intersected with its `slab` at
`be ± |be_error|`, so membership is the stored rows and slacks read as reals.

## Inputs
* `P` – H-polytope
* `x` – point of length `n`

## Hypotheses
* none

## Conclusion
* `x` lies in the nominal part iff it meets every inequality and equality up to its slack
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n} : -- --- CONCL ---
    x ∈ P.nominal.construct ↔
      (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i) + |toReal (P.b_error i)|)
        ∧ ∀ i, |(toRealMat P.Ae *ᵥ x) i - toReal (P.be i)|
          ≤ |toReal (P.be_error i)| := by -- --- PROOF ---
  -- three lemmas of the exact layer, in order, and the slab read as a distance
  rw [HPolytope.nominal, Real.HPolytope.mem_intersection_iff, Real.HPolytope.mem_ineqs_iff,
    Real.HPolytope.mem_slab_iff]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  show toReal (P.be i) - |toReal (P.be_error i)| ≤ _ ∧ _ ≤ toReal (P.be i) + |toReal (P.be_error i)|
    ↔ _
  rw [abs_le]
  exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
