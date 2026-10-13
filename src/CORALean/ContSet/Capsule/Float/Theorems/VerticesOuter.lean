import CORALean.ContSet.Capsule.Float.Operations.Vertices
import CORALean.ContSet.Capsule.Float.Theorems.ArcBoxMem
import CORALean.ContSet.Capsule.Float.Theorems.PiStepMem
import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Interval.Float.Theorems.Atan2LoLe
import CORALean.ContSet.Interval.Float.Theorems.Atan2HiLe
import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier

/-!
# Every box of `Capsule.vertices` holds a boundary point

For a capsule that is not a point and has a nonnegative radius, each box of the list holds a
sampled point of the exact layer's `vertices` of the nominal capsule, and that point is on the
frontier of the capsule (`vertices_mem_frontier`): the angles `θ ∓ π/2 + i π / 499` are enclosed,
`θ` by the corner values of the argument, and every interval operation encloses its exact
counterpart. The boxes enclose boundary points; they are not themselves on the boundary, and not
vertices.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vertices_outer (p k : ℕ) (C : Capsule 𝕋 2) (hr : 0 ≤ toReal C.r)
    (hnp : ¬ Real.Capsule.representsa_point C.nominal) :
    ∀ B ∈ C.vertices p k, ∃ x ∈ B.construct, x ∈ frontier C.construct := by -- --- PROOF ---
  -- the float test answers `false`, or the capsule would be a point
  have hfl : C.representsa_point = false := by
    by_contra hne
    have ht : C.representsa_point = true := by simpa using hne
    exact hnp ((Real.Capsule.representsa_point_iff (by norm_num) C.nominal).mp
      (Capsule.representsa_point_sound (by norm_num) ht))
  -- the angle `θ`, `π/2`, the step and the two centres, in their boxes
  have hθ : (fun _ => Complex.arg ⟨toReal (C.g 0), toReal (C.g 1)⟩ : Vec ℝ 1) ∈
      (⟨fun _ => Interval.atan2Lo p k (C.g 0) (C.g 1),
        fun _ => Interval.atan2Hi p k (C.g 0) (C.g 1)⟩ : Interval (Vec 𝕋 1)).construct :=
    fun _ => ⟨Interval.atan2Lo_le p k _ _, Interval.le_atan2Hi p k _ _⟩
  -- `π/2` in the box of `acos` at `0`
  have hq : (fun _ => Real.pi / 2 : Vec ℝ 1) ∈
      (⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩ : Interval (Vec 𝕋 1)).construct := by
    intro _
    refine ⟨?_, ?_⟩
    · have := acosDown_le p k (zero : 𝕋)
      rwa [toReal_zero, Real.arccos_zero] at this
    · have := le_acosUp p k (zero : 𝕋)
      rwa [toReal_zero, Real.arccos_zero] at this
  -- the step and the two centres
  have hstep := Capsule.piStep_mem (𝕋 := 𝕋) p k
  have hc₁ : (C.nominal.c + C.nominal.g : Vec ℝ 2) ∈
      (⟨fun j => addDown (C.c j) (C.g j), fun j => addUp (C.c j) (C.g j)⟩ :
        Interval (Vec 𝕋 2)).construct :=
    fun j => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  have hc₂ : (C.nominal.c - C.nominal.g : Vec ℝ 2) ∈
      (⟨fun j => subDown (C.c j) (C.g j), fun j => subUp (C.c j) (C.g j)⟩ :
        Interval (Vec 𝕋 2)).construct :=
    fun j => ⟨subDown_le_sub _ _, sub_le_subUp _ _⟩
  -- the base angles `θ - π/2` and `θ + π/2` in their boxes
  have hm : (fun _ => Complex.arg ⟨toReal (C.g 0), toReal (C.g 1)⟩ - Real.pi / 2 : Vec ℝ 1) ∈
      ((⟨fun _ => Interval.atan2Lo p k (C.g 0) (C.g 1),
        fun _ => Interval.atan2Hi p k (C.g 0) (C.g 1)⟩ : Interval (Vec 𝕋 1)).minus
        ⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩).construct :=
    Interval.minus_outer _ _ (Set.sub_mem_sub hθ hq)
  have hpl : (fun _ => Complex.arg ⟨toReal (C.g 0), toReal (C.g 1)⟩ + Real.pi / 2 : Vec ℝ 1) ∈
      ((⟨fun _ => Interval.atan2Lo p k (C.g 0) (C.g 1),
        fun _ => Interval.atan2Hi p k (C.g 0) (C.g 1)⟩ : Interval (Vec 𝕋 1)).plus
        ⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩).construct :=
    Interval.plus_outer _ _ (Set.add_mem_add hθ hq)
  unfold Capsule.vertices
  rw [if_neg (by simp [hfl])]
  dsimp only
  intro B hB
  simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hB
  -- the sampled point is in the box, and is a vertex of the exact layer, so on the frontier
  rcases hB with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · refine ⟨_, Capsule.arcBox_mem p (piStep p k) hstep _ _ C.r (i : ℕ) hc₁ hm, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inl (Or.inl ⟨i, rfl⟩)
  · refine ⟨_, Capsule.arcBox_mem p (piStep p k) hstep _ _ C.r (i : ℕ) hc₂ hpl, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inl (Or.inr ⟨i, rfl⟩)
  · refine ⟨_, Capsule.arcBox_mem p (piStep p k) hstep _ _ C.r 0 hc₁ hm, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inr (by simp; exact ⟨rfl, rfl⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
