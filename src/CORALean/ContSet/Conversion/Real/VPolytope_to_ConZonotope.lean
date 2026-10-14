module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ConZonotope

@[expose] public section

/-!
# A hull as a constrained zonotope

Exact, and cheap: the vertices become the generators, the centre is the origin,
and the constraint polytope is the standard simplex — coefficients nonnegative
and summing to one.

The unit box a constrained zonotope also imposes costs nothing here. A
nonnegative coefficient in a family summing to one is already at most one, so
`|βⱼ| ≤ 1` is implied rather than imposed, and no vertex is lost.

This is the direction that makes a constrained zonotope the general
representation: every bounded polytope is one, with no enclosure anywhere.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem VPolytope.mem_simplex_iff {k : ℕ} {β : Vec ℝ k} :
    β ∈ (VPolytope.simplex k).construct ↔ (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 := by -- --- PROOF ---
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h : -(β j) ≤ 0 := hle j
      linarith
    · -- restated at `Fin 1`, the row count's reduced spelling, so the index elaborates
      have heq' : ∀ _ : Fin 1, (∑ j, LinearMap.proj j : Vec ℝ k →ₗ[ℝ] ℝ) β = 1 := heq
      have h := heq' 0
      rwa [LinearMap.sum_apply] at h
  · rintro ⟨hnn, hsum⟩
    refine ⟨fun j => ?_, fun _ => ?_⟩
    · show -(β j) ≤ 0
      linarith [hnn j]
    · show (∑ j, LinearMap.proj j : Vec ℝ k →ₗ[ℝ] ℝ) β = 1
      rwa [LinearMap.sum_apply]


-- =======================================  MAIN THEOREM  ======================================= --

-- the vertices become generators at a zero centre, so the two sets coincide
theorem VPolytope.conZonotope_exact (P : VPolytope α) :
    P.construct = P.conZonotope.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, hnn, hsum, rfl⟩
    refine ⟨β, fun j => ?_, VPolytope.mem_simplex_iff.mpr ⟨hnn, hsum⟩, ?_⟩
    · rw [abs_of_nonneg (hnn j)]
      exact hsum ▸ Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    · show ∑ j, β j • P.V j = 0 + ∑ j, β j • P.V j
      rw [zero_add]
  · rintro ⟨β, -, hβ, rfl⟩
    obtain ⟨hnn, hsum⟩ := VPolytope.mem_simplex_iff.mp hβ
    refine ⟨β, hnn, hsum, ?_⟩
    show (0 : α) + ∑ j, β j • P.V j = ∑ j, β j • P.V j
    rw [zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
