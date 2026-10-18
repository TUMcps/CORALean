module

public import CORALean.ContSet.ConPolyZono.Float.Operations.MinkDiff
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeConPolyZonoContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic

@[expose] public section

/-!
# The float `minkDiff` of a constrained polynomial zonotope encloses the difference

`P ⊖ Z ⊆ minkDiff P Z`, as over ℝ (`minkDiff_outer`): a point `x` of the difference has
`x + c + Σ ±gⱼ ∈ P` at every corner of `Z`. Peeling the generators off in the order the fold
takes them, the points whose remaining corners all land in the current set lie in that set's
float translates by `±g` (`plus_outer`), so in their float cut (`intersection_outer`). The
corners are points of the nominal zonotope; when the error box holds `0` the float zonotope
holds them too, and the statement is about the whole float subtrahend.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float vector as a one-point set holds that point, read as reals. -/
theorem ConPolyZono.aux_mem_plus_point (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (w : Vec 𝕋 n) {y : Vec ℝ n}
    (hy : y - toRealVec w ∈ cPZ.construct) :
    y ∈ (cPZ.plus (Zonotope.point w).conPolyZono).construct := by
  refine ConPolyZono.plus_outer _ _ ⟨_, hy, toRealVec w, ?_, sub_add_cancel _ _⟩
  refine Zonotope.conPolyZono_contains _ ?_
  rw [Zonotope.construct_point]
  rfl

/-- The fold over the generators `g`: a point whose every corner `y + Σ ±gⱼ` lies in `A`, and
`A` in the start, lies in the result. -/
theorem ConPolyZono.aux_minkDiff_fold : -- --- STMT ---
    ∀ {m : ℕ} (g : Fin m → Vec 𝕋 n) (cur : ConPolyZono 𝕋 (Vec 𝕋 n)) (A : Set (Vec ℝ n)),
      A ⊆ cur.construct →
      {y | ∀ s : Fin m → Bool, y + ∑ j, (if s j then (1 : ℝ) else -1) • toRealVec (g j) ∈ A}
        ⊆ (Fin.foldl m (fun cPZ i => (cPZ.plus (Zonotope.point (g i)).conPolyZono).intersection
            (cPZ.plus (Zonotope.point (-(g i))).conPolyZono))
          cur).construct := by -- --- PROOF ---
  intro m
  induction m with
  | zero =>
    intro _ cur A hA y hy
    simpa using hA (by simpa using hy Fin.elim0)
  | succ m ih =>
    intro g cur A hA y hy
    rw [Fin.foldl_succ]
    -- the first generator's two translates of `A`, cut, hold the points `y` with `y ± g₀ ∈ A`
    refine ih (fun i => g i.succ) _
      {y | y + toRealVec (g 0) ∈ A ∧ y - toRealVec (g 0) ∈ A} ?_ ?_
    · rintro z ⟨hp, hm⟩
      refine ConPolyZono.intersection_outer _ _ ⟨?_, ?_⟩
      · exact ConPolyZono.aux_mem_plus_point _ _ (hA hm)
      · refine ConPolyZono.aux_mem_plus_point _ _ (hA ?_)
        have : z - toRealVec (-(g 0)) = z + toRealVec (g 0) := by
          rw [toRealVec_neg, sub_neg_eq_add]
        rw [this]
        exact hp
    · -- every corner of the rest, with `g₀` added or subtracted, is a corner of all of them
      intro s
      have hc : ∀ b : Bool, y + ∑ j : Fin (m + 1),
          (if (Fin.cons b s : Fin (m + 1) → Bool) j then (1 : ℝ) else -1) • toRealVec (g j) ∈ A :=
        fun b => hy _
      refine ⟨?_, ?_⟩
      · have h := hc true
        rw [Fin.sum_univ_succ] at h
        simpa [add_comm, add_left_comm, add_assoc] using h
      · have h := hc false
        rw [Fin.sum_univ_succ] at h
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer: `P ⊖ Z ⊆ minkDiff P Z` for a float subtrahend whose error box holds `0`. -/
theorem ConPolyZono.minkDiff_outer (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n))
    (h0 : (0 : Vec ℝ n) ∈ Z.I_error.construct) :
    minkowskiDiff cPZ₁.construct Z.construct ⊆ (cPZ₁.minkDiff Z).construct := by -- --- PROOF ---
  intro x hx
  refine ConPolyZono.aux_minkDiff_fold Z.G _
    {y | y + toRealVec Z.c ∈ cPZ₁.construct} ?_ ?_
  · -- the start: the minuend, made dependent, moved by `-c`
    intro y hy
    refine ConPolyZono.aux_mem_plus_point _ _ ?_
    rw [← ConPolyZono.dependent_exact]
    have : y - toRealVec (-Z.c) = y + toRealVec Z.c := by
      funext r
      simp [toRealVec, toReal_neg']
    rw [this]
    exact hy
  · -- every corner `c + Σ ±gⱼ` is a point of the float zonotope
    intro s
    have hz : toRealVec Z.c + ∑ j, (if s j then (1 : ℝ) else -1) • toRealVec (Z.G j)
        ∈ Z.construct := by
      refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => if s j then 1 else -1,
        fun j => by by_cases hs : s j <;> simp [hs], fun i => ?_⟩, 0, h0, add_zero _⟩
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toRealVec]
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    have := hx _ hz
    show x + _ + toRealVec Z.c ∈ cPZ₁.construct
    simpa [add_comm, add_left_comm, add_assoc] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
