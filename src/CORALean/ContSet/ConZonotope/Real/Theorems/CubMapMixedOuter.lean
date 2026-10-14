module

public import CORALean.ContSet.ConZonotope.Real.Operations.CubMapMixed
public import CORALean.ContSet.Zonotope.Real.Theorems.CubMapMixedCoeff
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# The mixed cubic map of constrained zonotopes is enclosed by `ConZonotope.cubMapMixed`

The coefficients of `Zonotope.cubMapMixed_coeff` carry each set's own `p` on its linear generators,
so each set's constraint holds there, and every other product factor is unconstrained. Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Mixed form, outer only; each set's constraints sit on its own linear generators. -/
theorem ConZonotope.cubMapMixed_outer (T : Fin m → Fin n → Mat ℝ n n)
    (cZ₁ cZ₂ cZ₃ : ConZonotope (Vec ℝ n)) :
    (fun x : Vec ℝ n × Vec ℝ n × Vec ℝ n => PolyZonotope.cubEvalMixed T x.1 x.2.1 x.2.2)
        '' (cZ₁.construct ×ˢ cZ₂.construct ×ˢ cZ₃.construct)
      ⊆ (ConZonotope.cubMapMixed T cZ₁ cZ₂ cZ₃).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x₁, x₂, x₃⟩, ⟨⟨p₁, hp₁, hP₁, rfl⟩, ⟨p₂, hp₂, hP₂, rfl⟩, ⟨p₃, hp₃, hP₃, rfl⟩⟩, rfl⟩
  obtain ⟨γ, hγ, h₁, h₂, h₃, hx⟩ := Zonotope.cubMapMixed_coeff T
    (⟨cZ₁.h, cZ₁.c, cZ₁.G⟩ : Zonotope (Vec ℝ n)) ⟨cZ₂.h, cZ₂.c, cZ₂.G⟩ ⟨cZ₃.h, cZ₃.c, cZ₃.G⟩
    p₁ p₂ p₃ hp₁ hp₂ hp₃
  -- the constraints, on the coefficients read as a plain vector
  have key : ∀ γ' : Vec ℝ ((cZ₃.h + 1) * (cZ₂.h + 1) * (cZ₁.h + 1)),
      ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
        (fun a : Fin cZ₁.h => ((0, 0), a.succ)) γ' = p₁
      → ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
          (fun b : Fin cZ₂.h => ((0, b.succ), 0)) γ' = p₂
      → ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
          (fun j : Fin cZ₃.h => ((j.succ, 0), 0)) γ' = p₃
      → γ' ∈ (((cZ₁.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun a : Fin cZ₁.h => ((0, 0), a.succ)))).intersection
          (cZ₂.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun b : Fin cZ₂.h => ((0, b.succ), 0))))).intersection
        (cZ₃.P.comap (ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
            (fun j : Fin cZ₃.h => ((j.succ, 0), 0))))).construct :=
    fun γ' e₁ e₂ e₃ => by
    -- one constraint polytope per set, each pulled back along its linear block
    refine HPolytope.mem_intersection_iff.mpr ⟨HPolytope.mem_intersection_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · show ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
        (fun a : Fin cZ₁.h => ((0, 0), a.succ)) γ' ∈ cZ₁.P.construct
      rw [e₁]; exact hP₁
    · show ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
        (fun b : Fin cZ₂.h => ((0, b.succ), 0)) γ' ∈ cZ₂.P.construct
      rw [e₂]; exact hP₂
    · show ConZonotope.cubLinearAt (cZ₃.h + 1) (cZ₂.h + 1) (cZ₁.h + 1)
        (fun j : Fin cZ₃.h => ((j.succ, 0), 0)) γ' ∈ cZ₃.P.construct
      rw [e₃]; exact hP₃
  exact ⟨γ, hγ, key γ (funext h₁) (funext h₂) (funext h₃), hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
