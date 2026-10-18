module

public import CORALean.ContSet.ConPolyZono.Real.Operations.RepresentsaPoint
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's `conPolyZono/representsa_(cPZ, 'point')` ignores the constraints

The branch `'point'` (l. 64-69, marked `% Todo: check constraints`) is
`res = isempty(cPZ.G) && isempty(cPZ.GI)`, with `S = cPZ.c` when it holds. Two wrong answers:

* no generator but an infeasible constraint: `c = 0`, one factor, `G` and `GI` empty and the
  constraint `α₁ = 2` (no `α₁ ∈ [-1, 1]` satisfies it) is the empty set, yet CORA answers `true`
  and returns the point `c`;
* a generator that the constraint pins down: `c = 0`, one factor, `G = (1)` with exponent `1` and
  the constraint `α₁ = 0` is the point `{0}`, yet CORA answers `false`.

Wrong answers, not unsound. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- No generator, the constraint `1 · α₁ = 2`: empty. -/
def ConPolyZono.aux_infeasible : ConPolyZono ℝ :=
  ⟨1, 0, 0, 1, 1, 0, Fin.elim0, fun _ _ => 0, Fin.elim0, fun _ _ => 1,
    fun _ => 2, fun _ _ => 1⟩

/-- `G = (1)` with exponent `1`, the constraint `1 · α₁ = 0`: the point `{0}`. -/
def ConPolyZono.aux_pinned : ConPolyZono ℝ :=
  ⟨1, 1, 0, 1, 1, 0, fun _ => 1, fun _ _ => 1, Fin.elim0, fun _ _ => 1,
    fun _ => 0, fun _ _ => 1⟩

theorem ConPolyZono.aux_infeasible_construct :
    ConPolyZono.aux_infeasible.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, β, ha, -, hs, -⟩
  have h4 := hs (0 : Fin 1)
  have h3 := ha (0 : Fin 1)
  simp [ConPolyZono.aux_infeasible, PolyZonotope.monomial, Matrix.mulVec, dotProduct] at h4 h3
  rw [h4] at h3
  norm_num [abs_of_pos] at h3

theorem ConPolyZono.aux_pinned_construct :
    ConPolyZono.aux_pinned.construct = {0} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨a, β, ha, -, hs, hx⟩
    have h1 := hs (0 : Fin 1)
    simp [ConPolyZono.aux_pinned, PolyZonotope.monomial, Matrix.mulVec, dotProduct] at h1 hx
    exact hx.trans h1
  · intro hx
    refine ⟨fun _ => 0, Fin.elim0, fun _ => by norm_num, fun j => j.elim0, ?_, ?_⟩
    · intro i
      simp [ConPolyZono.aux_pinned, PolyZonotope.monomial, Matrix.mulVec, dotProduct]
    · simp [ConPolyZono.aux_pinned, PolyZonotope.monomial, Set.mem_singleton_iff.mp hx]


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA says "point" for an empty set and "no point" for a point. -/
theorem ConPolyZono.representsa_point_cora_counterexample : -- --- STMT ---
    (ConPolyZono.aux_infeasible.construct = ∅ ∧
        ConPolyZono.aux_infeasible.representsa_point = true) ∧
      (ConPolyZono.aux_pinned.construct = {0} ∧
        ConPolyZono.aux_pinned.representsa_point = false) := by -- --- PROOF ---
  refine ⟨⟨ConPolyZono.aux_infeasible_construct, ?_⟩, ⟨ConPolyZono.aux_pinned_construct, ?_⟩⟩
  · simp [ConPolyZono.representsa_point, ConPolyZono.aux_infeasible]
  · simp [ConPolyZono.representsa_point, ConPolyZono.aux_pinned]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
