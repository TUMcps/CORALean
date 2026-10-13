module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import CORALean.ContSet.Zonotope.Real.Theorems.MemScaleIff

@[expose] public section

/-!
# A stretched template, by its template's halfspaces

`Zonotope.mem_scale_iff` at a generator family over any finite index: the template is
renumbered into a `Fin` by `Fintype.equivFin`, which changes neither the set, nor the
span, nor which cross products occur. This is the halfspace form [1, Thm. 1],
[2, Thm. 1] and [3, Lemma 3] turn the conformance constraint into: linear in the
centre and in the stretch factors, at normals fixed by the template alone. It is also
[1, Remark 1]: the halfspaces of `W` and `V` make [1, Cor. 1]'s inclusions linear.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
* [3] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Membership in `⟨c, G diag(α)⟩`, `α ≥ 0`, is the template's halfspaces at offsets
linear in `α`. -/
theorem Conform.mem_templateZono_iff {m : ℕ} {ι κ : Type} [Fintype ι] (c : Vec ℝ (m + 1))
    (G : ι → Vec ℝ (m + 1)) (hspan : Submodule.span ℝ (Set.range G) = ⊤)
    (N : κ → Vec ℝ (m + 1)) (hN : Conform.HasNormals G N) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j)
    (y : Vec ℝ (m + 1)) :
    y ∈ Conform.templateZono c G α ↔
      ∀ i, N i ⬝ᵥ (y - c) ≤ ∑ j, |N i ⬝ᵥ G j| * α j := by -- --- PROOF ---
  -- renumber the template into a `Fin`, where `Zonotope.mem_scale_iff` applies
  let e := Fintype.equivFin ι
  let Z : Real.Zonotope (Vec ℝ (m + 1)) := ⟨Fintype.card ι, c, fun t => G (e.symm t)⟩
  have hspanZ : Submodule.span ℝ (Set.range Z.G) = ⊤ := by
    rw [← hspan]
    congr 1
    exact (e.symm.surjective.range_comp G)
  have hNZ : ∀ S : Fin m → Fin Z.h, ∃ (i₁ i₂ : κ) (lam : ℝ), 0 < lam ∧
      N i₁ = lam • Z.facetNormal S ∧ N i₂ = -(lam • Z.facetNormal S) := fun S =>
    hN (fun b => e.symm (S b))
  have h := Z.mem_scale_iff hspanZ N hNZ (fun t => α (e.symm t)) (fun t => hα _) y
  -- the set and the offsets are the same under the renumbering
  have hset : y ∈ Conform.templateZono c G α ↔
      y ∈ (⟨Z.h, Z.c, fun t => α (e.symm t) • Z.G t⟩ :
        Real.Zonotope (Vec ℝ (m + 1))).construct := by
    constructor
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨fun t => β (e.symm t), fun t => hβ _, ?_⟩
      simp only [Z]
      congr 1
      exact (e.symm.sum_comp fun j => β j • α j • G j).symm
    · -- back along the bijection
      rintro ⟨β, hβ, rfl⟩
      refine ⟨fun j => β (e j), fun j => hβ _, ?_⟩
      simp only [Z]
      congr 1
      rw [← e.symm.sum_comp]
      simp
  have hoff : ∀ i, ∑ t, |N i ⬝ᵥ Z.G t| * α (e.symm t) = ∑ j, |N i ⬝ᵥ G j| * α j := fun i =>
    e.symm.sum_comp fun j => |N i ⬝ᵥ G j| * α j
  rw [hset, h]
  simp only [hoff]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
