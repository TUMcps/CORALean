module

public import CORALean.ContSet.Capsule.Float.Operations.Vertices
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointParts

@[expose] public section

/-!
# `Capsule.vertices` of a point capsule

Where the float test certifies a point capsule, the list is the one box `[c, c]`, and its point
`c` is the exact layer's single vertex, on the frontier of the capsule.

## Inputs
* `p` – precision of atan2 and acos
* `k` – Newton steps for sqrt
* `C` – planar capsule

## Hypotheses
* `h` – capsule certified a point

## Conclusion
* the vertex list is the single box at the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vertices_point (p k : ℕ) {C : Capsule 𝕋 2}
    (h : C.representsa_point = true) : -- --- CONCL ---
    C.vertices p k = [Interval.point C.c] ∧
      ∃ x ∈ (Interval.point C.c).construct, x ∈ frontier C.construct := by -- --- PROOF ---
  refine ⟨by simp [Capsule.vertices, h], ?_⟩
  -- the box is the origin, and the nominal capsule a point
  obtain ⟨hI, hn⟩ := Capsule.representsa_point_parts h
  rw [Capsule.construct_eq_nominal hI]
  refine ⟨toRealVec C.c, fun _ => ⟨le_rfl, le_rfl⟩, ?_⟩
  have hr : 0 ≤ C.nominal.r := le_of_eq (Eq.symm hn.2)
  refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
  simp [Real.Capsule.vertices, hn]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
