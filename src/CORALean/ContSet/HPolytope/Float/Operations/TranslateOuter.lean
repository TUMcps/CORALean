module

public import CORALean.ContSet.HPolytope.Float.Operations.Translate
public import CORALean.ContSet.HPolytope.Float.Theorems.AnchorEqsOuter

@[expose] public section

/-!
# `HPolytope.translate` encloses

Each bound shifts by what its own row reads of the shift, rounded outward; the box shifts
with the nominal part. A shifted point of the nominal part reads, on an equality row, between the
two roundings of its shifted bound, which is the residual `anchorEqs` is given
(`HPolytope.anchorEqs_outer`).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.translate_outer (t : Vec 𝕋 n) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    (toRealVec t + ·) '' P.construct ⊆ (HPolytope.translate t P).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, e, he, rfl⟩ := Set.mem_add.mp hy
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hz
  show toRealVec t + (z + e) ∈ _
  rw [← add_assoc]
  -- a row reads the shifted point as what it read of each part
  have hsplit : ∀ {m : ℕ} (M : Mat 𝕋 m n) (i : Fin m),
      (toRealMat M *ᵥ (toRealVec t + z)) i
        = (∑ j, toReal (M i j) * toReal (t j)) + (toRealMat M *ᵥ z) i := by
    intro m M i
    rw [Matrix.mulVec_add]
    rfl
  refine HPolytope.anchorEqs_outer _ _ (fun i => ?_) (fun i => ?_) he
  -- each inequality bound shifts by what its own row reads of `t`, rounded up
  · show (toRealMat P.A *ᵥ (toRealVec t + z)) i ≤ toReal (addUp (P.b i) (dotUp (P.A i) t))
    rw [hsplit P.A i]
    have h := add_le_addUp (P.b i) (dotUp (P.A i) t)
    have h' := le_dotUp (P.A i) t
    linarith [hle i]
  -- an equality reads between the two roundings of its shifted bound
  · show |(toRealMat P.Ae *ᵥ (toRealVec t + z)) i - toReal (addUp (P.be i) (dotUp (P.Ae i) t))|
      ≤ toReal (subUp (addUp (P.be i) (dotUp (P.Ae i) t)) (addDown (P.be i) (dotDown (P.Ae i) t)))
    rw [hsplit P.Ae i, heq i]
    have h1 := add_le_addUp (P.be i) (dotUp (P.Ae i) t)
    have h2 := le_dotUp (P.Ae i) t
    have h3 := addDown_le_add (P.be i) (dotDown (P.Ae i) t)
    have h4 := dotDown_le (P.Ae i) t
    have h5 := sub_le_subUp (addUp (P.be i) (dotUp (P.Ae i) t))
      (addDown (P.be i) (dotDown (P.Ae i) t))
    rw [abs_le]
    constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
