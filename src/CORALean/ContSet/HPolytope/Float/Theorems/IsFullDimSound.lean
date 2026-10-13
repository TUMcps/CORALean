module

public import CORALean.ContSet.HPolytope.Float.Operations.IsFullDim
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# A `true` from `HPolytope.isFullDim` proves an interior point

Read as reals, the proposed point satisfies every inequality strictly. The set of points that do
is open (finitely many strict inequalities between continuous functions) and inside the polytope,
so the point is interior.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to a point is continuous in the point. -/
theorem HPolytope.aux_continuous_row {m : ℕ} (M : Mat ℝ m n) (i : Fin m) :
    Continuous fun x : Vec ℝ n => (M *ᵥ x) i :=
  (continuous_finsetSum Finset.univ fun j _ =>
    (continuous_const : Continuous fun _ : Vec ℝ n => M i j).mul (continuous_apply j))


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isFullDim_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {x₀ : Vec 𝕋 n}
    (h : P.isFullDim x₀ = true) : (interior P.construct).Nonempty := by -- --- PROOF ---
  simp only [HPolytope.isFullDim, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨h1, h2⟩ := h
  let U : Set (Vec ℝ n) := {x | (∀ i, (toRealMat P.A *ᵥ x) i < toReal (P.b i))
    ∧ ∀ i, toReal (P.be.inf i) < (toRealMat P.Ae *ᵥ x) i
      ∧ (toRealMat P.Ae *ᵥ x) i < toReal (P.be.sup i)}
  -- the strict inequalities define an open set
  have hU : IsOpen U := by
    have e1 : IsOpen {x : Vec ℝ n | ∀ i, (toRealMat P.A *ᵥ x) i < toReal (P.b i)} := by
      have : {x : Vec ℝ n | ∀ i, (toRealMat P.A *ᵥ x) i < toReal (P.b i)}
          = ⋂ i, {x | (toRealMat P.A *ᵥ x) i < toReal (P.b i)} := by ext; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_lt (HPolytope.aux_continuous_row _ i) continuous_const
    have e2 : IsOpen {x : Vec ℝ n | ∀ i, toReal (P.be.inf i) < (toRealMat P.Ae *ᵥ x) i
        ∧ (toRealMat P.Ae *ᵥ x) i < toReal (P.be.sup i)} := by
      have : {x : Vec ℝ n | ∀ i, toReal (P.be.inf i) < (toRealMat P.Ae *ᵥ x) i
          ∧ (toRealMat P.Ae *ᵥ x) i < toReal (P.be.sup i)}
          = ⋂ i, ({x | toReal (P.be.inf i) < (toRealMat P.Ae *ᵥ x) i}
              ∩ {x | (toRealMat P.Ae *ᵥ x) i < toReal (P.be.sup i)}) := by ext; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        (isOpen_lt continuous_const (HPolytope.aux_continuous_row _ i)).inter
          (isOpen_lt (HPolytope.aux_continuous_row _ i) continuous_const)
    exact e1.inter e2
  -- which lies inside the polytope and contains the proposed point
  have hsub : U ⊆ P.construct := fun x hx =>
    HPolytope.mem_construct_iff.mpr ⟨fun i => (hx.1 i).le,
      fun i => ⟨(hx.2 i).1.le, (hx.2 i).2.le⟩⟩
  have hx₀ : toRealVec x₀ ∈ U := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := toReal_lt_of_ltStrict (h1 i)
      exact lt_of_le_of_lt (le_dotUp (P.A i) x₀) this
    · have a := toReal_lt_of_ltStrict (h2 i).1
      have b := toReal_lt_of_ltStrict (h2 i).2
      exact ⟨lt_of_lt_of_le a (dotDown_le (P.Ae i) x₀), lt_of_le_of_lt (le_dotUp (P.Ae i) x₀) b⟩
  exact ⟨_, interior_maximal hsub hU hx₀⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
