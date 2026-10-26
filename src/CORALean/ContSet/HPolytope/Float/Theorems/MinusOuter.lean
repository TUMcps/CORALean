module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.Translate
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSetRhsNominal

@[expose] public section

/-!
# `HPolytope.minus` encloses

Every point of the polytope less the subtrahend lies in the result: negation is
exact, so this is `aux_translate_outer` at `-v`.

## Inputs
* `P` – H-polytope
* `v` – vector of length `n`

## Hypotheses
* none

## Conclusion
* the image of `P` shifted by `-v` is contained in `P.minus v`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Pointwise Matrix

/-- The shifted polytope contains the shift of every point. -/
private theorem HPolytope.aux_translate_outer (t : Vec 𝕋 n)
    (P : HPolytope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
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

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minus_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) : -- --- CONCL ---
    (· - toRealVec v) '' P.construct ⊆ (P.minus v).construct := by -- --- PROOF ---
  have h := HPolytope.aux_translate_outer (-v) P
  have hneg : toRealVec (-v) = -toRealVec v := toRealVec_neg _
  rw [hneg] at h
  show _ ⊆ (HPolytope.translate (-v) P).construct
  simpa only [sub_eq_add_neg, add_comm _ (-toRealVec v)] using h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
