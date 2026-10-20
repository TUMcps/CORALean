module

public import CORALean.ContSet.HPolytope.Float.Operations.Translate
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSetRhsNominal

@[expose] public section

/-!
# `HPolytope.translate` encloses

Each bound shifts by what its own row reads of the shift, between its two roundings; the box
shifts with the nominal part. A shifted point of the nominal part reads each row within its slack
of the exact shifted bound, which lies between those roundings, so it is in the nominal part
`setRhs` builds (`HPolytope.mem_setRhs_nominal`).

## Inputs
* `t` – vector of length `n`
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* the shifted polytope contains the shift of every point
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The shifted polytope contains the shift of every point. -/
theorem HPolytope.translate_outer (t : Vec 𝕋 n) (P : HPolytope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
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
  have hlo : ∀ (a : Vec 𝕋 n) (c : 𝕋), toReal (addDown c (dotDown a t))
      ≤ toReal c + ∑ j, toReal (a j) * toReal (t j) := fun a c =>
    (addDown_le_add c (dotDown a t)).trans (by linarith [dotDown_le a t])
  have hhi : ∀ (a : Vec 𝕋 n) (c : 𝕋), toReal c + ∑ j, toReal (a j) * toReal (t j)
      ≤ toReal (addUp c (dotUp a t)) := fun a c =>
    le_trans (by linarith [le_dotUp a t]) (add_le_addUp c (dotUp a t))
  -- each row's exact shifted bound lies between its two roundings; the box is kept
  refine Set.add_mem_add (HPolytope.mem_setRhs_nominal P
    (fun i => toReal (P.b i) + ∑ j, toReal (P.A i j) * toReal (t j))
    (fun i => toReal (P.be i) + ∑ j, toReal (P.Ae i j) * toReal (t j))
    (fun i => ⟨hlo _ _, hhi _ _⟩) (fun i => ⟨hlo _ _, hhi _ _⟩) (fun i => ?_) (fun i => ?_)) he
  · rw [hsplit P.A i]
    linarith [hle i]
  · rw [hsplit P.Ae i]
    have h := heq i
    rwa [show (∑ j, toReal (P.Ae i j) * toReal (t j)) + (toRealMat P.Ae *ᵥ z) i
        - (toReal (P.be i) + ∑ j, toReal (P.Ae i j) * toReal (t j))
        = (toRealMat P.Ae *ᵥ z) i - toReal (P.be i) by ring]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
