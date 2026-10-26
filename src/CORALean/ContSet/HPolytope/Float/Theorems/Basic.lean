module

public import CORALean.ContSet.HPolytope.Float.Definitions.Basic
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
public import CORALean.ContSet.HPolytope.Float.Operations.EqVec
public import CORALean.ContSet.HPolytope.Float.Operations.Materialise
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructCongr
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ContSet/HPolytope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =============================  `HPolytope.isErrFree_of_origin`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---

/-- A polytope whose box is the origin and whose slacks are `zero` is error-free. -/
theorem HPolytope.isErrFree_of_origin {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.I_error = Interval.origin n) (hb : P.b_error = fun _ => FloatOps.zero)
    (he : P.be_error = fun _ => FloatOps.zero) : P.IsErrFree :=
  ⟨fun _ => h ▸ ⟨toReal_zero, toReal_zero⟩, fun _ => hb ▸ toReal_zero, fun _ => he ▸ toReal_zero⟩


-- ============================  `HPolytope.mem_nominal_of_origin`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A polytope with the origin box is read at its nominal part. -/
theorem HPolytope.mem_nominal_of_origin {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.I_error = Interval.origin n) {x : Vec ℝ n} :
    x ∈ P.construct ↔ x ∈ P.nominal.construct :=
  Set.ext_iff.mp (HPolytope.construct_eq_nominal fun _ => h ▸ ⟨toReal_zero, toReal_zero⟩) x


-- ============================  `HPolytope.toReal_eq_of_eqScalar`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eqScalar a b = true` gives `toReal a = toReal b`, each `le` being sound. -/
theorem HPolytope.toReal_eq_of_eqScalar {a b : 𝕋} (h : HPolytope.eqScalar a b = true) :
    toReal a = toReal b := by
  simp only [HPolytope.eqScalar, Bool.and_eq_true] at h
  exact le_antisymm (toReal_le_of_le h.1) (toReal_le_of_le h.2)


-- ==============================  `HPolytope.toReal_eq_of_eqVec`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Entry by entry, so the dot product with any point agrees. -/
theorem HPolytope.toReal_eq_of_eqVec {u v : Vec 𝕋 n} (h : HPolytope.eqVec u v = true) (j : Fin n) :
    toReal (u j) = toReal (v j) :=
  HPolytope.toReal_eq_of_eqScalar (List.all_eq_true.mp h j (List.mem_finRange j))

end


section

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `HPolytope.materialise_eq`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem HPolytope.materialise_eq (P : HPolytope 𝕋 (Vec 𝕋 n)) : P.materialise = P := by
  simp [HPolytope.materialise]

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
