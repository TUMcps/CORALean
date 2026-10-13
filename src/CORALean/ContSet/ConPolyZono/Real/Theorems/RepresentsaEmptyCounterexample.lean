import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# CORA's `representsa_(cPZ, 'emptySet')` answers "not empty" before reading the constraints

CORA's `@conPolyZono/representsa_.m`, `aux_isEmptySet`, begins with
`if ~isempty(cPZ.GI): res = false; return`, that is, "not empty" as soon as the independent
generators are nonempty, before the constraints are looked at. A constrained polynomial zonotope
is empty whenever its constraints have no solution in the box, whatever `GI` is.

The example has one factor, no dependent generators, one independent generator `GI = 1` and the
constraint `α₁ = 2`, which no `α₁ ∈ [-1, 1]` satisfies. `ConPolyZono.construct` is `∅`, and the
printed check answers `false`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The part of `aux_isEmptySet` that precedes the contractor: `some false` ("not empty") when
`GI` is nonempty, `none` for the rest (the constraint check and the contraction of the domain,
which are not modelled). -/
def ConPolyZono.aux_isEmptySetPrinted {α : Type} (cPZ : ConPolyZono α) : Option Bool :=
  let giNonempty := decide (0 < cPZ.q)
  if giNonempty then some false else none


/-- One factor, `c = 0`, `GI = 1`, and the constraint `1 · α₁ = 2`. -/
def ConPolyZono.aux_emptyWithGI : ConPolyZono ℝ :=
  ⟨1, 0, 1, 1, 1, 0, Fin.elim0, fun _ _ => 0, fun _ => 1, fun _ _ => 1,
    ⟨fun _ => 2, fun _ => 2⟩, fun _ _ => 1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is empty although `GI` is nonempty, and CORA's printed check answers "not empty". -/
theorem ConPolyZono.representsa_empty_counterexample :
    0 < ConPolyZono.aux_emptyWithGI.q ∧ ConPolyZono.aux_emptyWithGI.construct = ∅ ∧
      ConPolyZono.aux_isEmptySetPrinted ConPolyZono.aux_emptyWithGI
        = some false := by -- --- PROOF ---
  refine ⟨Nat.one_pos, ?_,
    by simp [ConPolyZono.aux_isEmptySetPrinted, ConPolyZono.aux_emptyWithGI]⟩
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, β, ha, -, hs, -⟩
  have h1 := (hs (0 : Fin 1)).1
  have h2 := (hs (0 : Fin 1)).2
  have h3 := ha (0 : Fin 1)
  simp [ConPolyZono.aux_emptyWithGI, PolyZonotope.monomial, Matrix.mulVec, dotProduct] at h1 h2 h3
  have h4 := le_antisymm h2 h1
  rw [h4] at h3
  norm_num [abs_of_pos] at h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
