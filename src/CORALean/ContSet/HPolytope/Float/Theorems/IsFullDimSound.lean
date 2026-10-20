module

public import CORALean.ContSet.HPolytope.Float.Operations.IsFullDim
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A `true` from `HPolytope.isFullDim` proves an interior point

Read as reals, the proposed point satisfies every inequality strictly. The set of points that do
is open (finitely many strict inequalities between continuous functions) and inside the nominal
part, so the point is interior to it; shifted by a point of the (non-empty) error box it is
interior to the sum.

## Inputs
* `P` – H-polytope
* `x₀` – point of length `n`

## Hypotheses
* `h` – `P.isFullDim x₀` holds

## Conclusion
* A `true` from `HPolytope.isFullDim` proves an interior point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to a point is continuous in the point. -/
theorem HPolytope.aux_continuous_row {m : ℕ} (M : Mat ℝ m n) (i : Fin m) :
    Continuous fun x : Vec ℝ n => (M *ᵥ x) i :=
  (continuous_finsetSum Finset.univ fun j _ =>
    (continuous_const : Continuous fun _ : Vec ℝ n => M i j).mul (continuous_apply j))


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isFullDim_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {x₀ : Vec 𝕋 n}
    (h : P.isFullDim x₀ = true) : -- --- CONCL ---
    (interior P.construct).Nonempty := by -- --- PROOF ---
  simp only [HPolytope.isFullDim, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨hme, h1⟩, hbox⟩ := h
  let U : Set (Vec ℝ n) := {x | ∀ i, (toRealMat P.A *ᵥ x) i < toReal (P.b i)}
  -- the strict inequalities define an open set
  have hU : IsOpen U := by
    have : U = ⋂ i, {x | (toRealMat P.A *ᵥ x) i < toReal (P.b i)} := by ext; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (HPolytope.aux_continuous_row _ i) continuous_const
  -- which lies inside the nominal part, there being no equality row
  have hsub : U ⊆ P.nominal.construct := fun x hx =>
    HPolytope.mem_nominal_iff.mpr
      ⟨fun i => (hx i).le.trans (le_add_of_nonneg_right (abs_nonneg _)), fun i => (hme ▸ i).elim0⟩
  -- shifted by a point of the error box, it lies inside the polytope
  have he : (fun j => toReal (P.I_error.inf j)) ∈ P.I_error.construct :=
    Interval.mem_vec_iff.mpr fun j => ⟨le_rfl, toReal_le_of_le (hbox j)⟩
  have hV : IsOpen ((fun u => u + fun j => toReal (P.I_error.inf j)) '' U) :=
    (Homeomorph.addRight (fun j => toReal (P.I_error.inf j))).isOpenMap U hU
  have hsub' : (fun u => u + fun j => toReal (P.I_error.inf j)) '' U ⊆ P.construct := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hsub hu, _, he, rfl⟩
  have hx₀ : toRealVec x₀ + (fun j => toReal (P.I_error.inf j))
      ∈ (fun u => u + fun j => toReal (P.I_error.inf j)) '' U := by
    refine ⟨toRealVec x₀, fun i => ?_, rfl⟩
    have := toReal_lt_of_ltStrict (h1 i)
    exact lt_of_le_of_lt (le_dotUp (P.A i) x₀) this
  exact ⟨_, interior_maximal hsub' hV hx₀⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
