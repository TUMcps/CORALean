import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A zonotope is full-dimensional iff its generators span

The zonotope is the translate by `c` of the image of the cube `[-1, 1]^h` under the linear map
`β ↦ ∑ βⱼ Gⱼ`. If the generators span, that map is onto, hence open, and the image of the open cube
is an open set around `c`. If they do not, the zonotope lies in a translate of a proper subspace,
which has no interior (`Submodule.eq_top_of_nonempty_interior'`).

Stated at `construct`, which is what `ContSet.IsFullDim` unfolds to: the `ContSet` instance is
declared after the theorems. Over any finite-dimensional real normed space, in particular `Vec ℝ n`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isFullDim_iff (Z : Zonotope α) :
    (interior Z.construct).Nonempty ↔ Submodule.span ℝ (range Z.G) = ⊤ := by -- --- PROOF ---
  let L : (Fin Z.h → ℝ) →ₗ[ℝ] α := Fintype.linearCombination ℝ Z.G
  have hL : ∀ β, L β = ∑ j, β j • Z.G j := fun β => by
    simp [L, Fintype.linearCombination_apply]
  have hrange : LinearMap.range L = Submodule.span ℝ (range Z.G) :=
    Fintype.range_linearCombination ℝ Z.G
  have hsub : Z.construct ⊆ (fun v => Z.c + v) '' (LinearMap.range L : Set α) := by
    rintro x ⟨β, -, rfl⟩
    exact ⟨L β, ⟨β, rfl⟩, by rw [hL]⟩
  constructor
  · rintro ⟨y, hy⟩
    have h1 := interior_mono hsub hy
    have h1' : y ∈ (Homeomorph.addLeft Z.c) '' interior (LinearMap.range L : Set α) := by
      rw [Homeomorph.image_interior]; exact h1
    have h2 : (interior (LinearMap.range L : Set α)).Nonempty := by
      obtain ⟨v, hv, -⟩ := h1'
      exact ⟨v, hv⟩
    -- a subspace with an interior point is the whole space
    rw [← hrange]
    exact Submodule.eq_top_of_nonempty_interior' _ h2
  · -- spanning generators: the linear map is onto, hence open, so the open cube maps to an open set
    intro htop
    have hsurj : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, hrange]; exact htop
    have hopen : IsOpenMap L := L.isOpenMap_of_finiteDimensional hsurj
    let U : Set (Fin Z.h → ℝ) := {β | ∀ j, |β j| < 1}
    have hU : IsOpen U := by
      have : U = Set.pi univ fun j => Metric.ball (0 : ℝ) 1 := by
        ext β; simp [U, Set.mem_pi]
      rw [this]
      exact isOpen_set_pi Set.finite_univ fun j _ => Metric.isOpen_ball
    have hV : IsOpen ((fun v => Z.c + v) '' (L '' U)) :=
      (Homeomorph.addLeft Z.c).isOpenMap _ (hopen _ hU)
    have hVsub : (fun v => Z.c + v) '' (L '' U) ⊆ Z.construct := by
      rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
      exact ⟨β, fun j => (hβ j).le, by rw [hL]⟩
    refine ⟨Z.c, interior_maximal hVsub hV ?_⟩
    exact ⟨0, ⟨0, fun j => by simp, map_zero L⟩, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
