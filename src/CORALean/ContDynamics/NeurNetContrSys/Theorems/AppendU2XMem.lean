module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.AppendU2X
public import CORALean.ContSet.Interval.Float.Theorems.AppendToSet
public import CORALean.ContSet.Zonotope.Float.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Theorems.MemToSetIffContainsAt

@[expose] public section

/-!
# The joint set holds the state and the network's output

`appendU2X` shares the generators of the state set with the first ones of the image: the column
`j` of `[X.G 0; U.G]` is `X.G j` over `U.G j`. A point `x` of `X` at the weights `β` is mapped to
the image's point at weights that begin with `β` (`Zonotope.Tracks`), and the stacked point is
the joint set's at those same weights, the error boxes being stacked ([1, Alg. 2], line 4).

## Inputs
* `X` – state set
* `U` – network image of the state set
* `π` – controller function

## Hypotheses
* `hπ` – the image tracks the controller over the state set

## Conclusion
* the state and the controller's output, stacked, lie in the joint set

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.appendU2X_mem {X : Zonotope (Vec 𝕋 n)} {U : Zonotope (Vec 𝕋 m)}
    {π : Vec ℝ n → Vec ℝ m} (hπ : X.Tracks U π) : -- --- CONCL ---
    ∀ J ∈ NeurNetContrSys.appendU2X X U, ∀ x ∈ X.toSet,
      (Fin.append x (π x) : Vec ℝ (n + m)) ∈ J.toSet := by -- --- PROOF ---
  intro J hJ x hx
  obtain ⟨hle, H⟩ := hπ
  obtain ⟨β, hβ⟩ := Zonotope.mem_toSet_iff_containsAt.mp hx
  obtain ⟨γ, hγ, hy⟩ := H β x hβ
  simp only [Option.mem_def, NeurNetContrSys.appendU2X, hle, if_true, Option.some.injEq] at hJ
  subst hJ
  obtain ⟨-, eX, heX, hxX⟩ := hβ
  obtain ⟨hγ1, eU, heU, hxU⟩ := hy
  refine Zonotope.mem_toSet_iff_containsAt.mpr ⟨γ, hγ1, Fin.append eX eU, ?_, fun i => ?_⟩
  · -- the error box is the two boxes side by side
    rw [Interval.append_toSet]
    exact ⟨(eX, eU), ⟨heX, heU⟩, rfl⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · -- the state half: the generators of `X` are `J`'s first, the others are zero there
      have hsum : ∑ j : Fin U.h, toReal ((if hj : j.val < X.h then X.G ⟨j.val, hj⟩ else
          fun _ => zero) i) * γ j = ∑ j, toReal (X.G j i) * β j := by
        refine (Fintype.sum_of_injective (Fin.castLE hle) (Fin.castLE_injective hle) _ _ ?_ ?_).symm
        · intro j hj
          have hjX : ¬ j.val < X.h := fun hlt => hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
          simp [hjX, toReal_zero]
        · intro j
          simp [hγ j]
      show _ = toReal (Fin.append X.c U.c (Fin.castAdd m i)) + ∑ j : Fin U.h, toReal (Fin.append
        (if hj : j.val < X.h then X.G ⟨j.val, hj⟩ else fun _ => zero) (U.G j)
          (Fin.castAdd m i)) * γ j + _
      simp only [Fin.append_left]
      rw [hsum, hxX i]
    · -- the output half: `U`'s own center, generators and box
      show _ = toReal (Fin.append X.c U.c (Fin.natAdd n i)) + ∑ j : Fin U.h, toReal (Fin.append
        (if hj : j.val < X.h then X.G ⟨j.val, hj⟩ else fun _ => zero) (U.G j)
          (Fin.natAdd n i)) * γ j + _
      simp only [Fin.append_right]
      exact hxU i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
