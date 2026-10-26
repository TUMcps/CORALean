module

public import CORALean.ContSet.Capsule.Float.Operations.Vertices
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.CosOuter
public import CORALean.ContSet.Interval.Float.Theorems.SinOuter
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Interval.Float.Theorems.Atan2LoLe
public import CORALean.ContSet.Interval.Float.Theorems.Atan2HiLe
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointParts

@[expose] public section

/-!
# Every box of `Capsule.vertices` holds a boundary point

For a capsule that is not a point, has a nonnegative radius and an error box that is the origin
(the boundary of a capsule thickened by a box is not sampled), each box of the list holds a
sampled point of the exact layer's `vertices` of the nominal capsule, and that point is on the
frontier of the capsule (`vertices_mem_frontier`): the angles `θ ∓ π/2 + i π / 499` are enclosed,
`θ` by the corner values of the argument, and every interval operation encloses its exact
counterpart. The boxes enclose boundary points; they are not themselves on the boundary, and not
vertices.

## Inputs
* `p` – precision of atan2 and acos
* `k` – Newton steps for sqrt
* `C` – planar capsule

## Hypotheses
* `hr` – radius nonnegative
* `hnp` – nominal capsule is not a point
* `hI` – error box is the origin

## Conclusion
* every vertex box holds a boundary point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Capsule.piStep` brackets `π / 499`. -/
private theorem Capsule.aux_piStep_mem (p k : ℕ) : -- --- CONCL ---
    toReal (Capsule.piStep (𝕋 := 𝕋) p k).inf ≤ Real.pi / 499 ∧
      Real.pi / 499 ≤ toReal (Capsule.piStep (𝕋 := 𝕋) p k).sup := by -- --- PROOF ---
  have hm : toReal (acosDown p k (zero : 𝕋)) ≤ Real.pi / 2 := by
    have := acosDown_le p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hp : Real.pi / 2 ≤ toReal (acosUp p k (zero : 𝕋)) := by
    have := le_acosUp p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hpi := Real.pi_pos
  -- the divisors: `499` between `intDown` and `intUp`
  have hu : (499 : ℝ) ≤ toReal (intUp 499 : 𝕋) := by
    have := (intDown_le_intUp (𝕋 := 𝕋) 499).2
    simpa using this
  have hd : toReal (intDown 499 : 𝕋) ≤ 499 := by
    have := (intDown_le_intUp (𝕋 := 𝕋) 499).1
    simpa using this
  have hLo := addDown_le_add (acosDown p k (zero : 𝕋)) (acosDown p k zero)
  have hHi := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  unfold Capsule.piStep
  dsimp only
  constructor
  · -- from below: the quotient by a divisor at least `499`
    refine le_trans (divDown_le_div _ _ (by linarith)) ?_
    by_cases h : toReal (addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero)) ≤ 0
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h (by linarith)) (by positivity)
    · push Not at h
      exact le_trans (div_le_div_of_nonneg_left h.le (by norm_num) hu)
        (div_le_div_of_nonneg_right (by linarith) (by norm_num))
  · split_ifs with hc
    · -- from above: the divisor positive and at most `499`
      have hpos : 0 < toReal (intDown 499 : 𝕋) := by
        simpa [toReal_zero] using toReal_lt_of_ltStrict hc
      refine le_trans ?_ (div_le_divUp _ _ hpos)
      exact le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num))
        (div_le_div_of_nonneg_left (by linarith) hpos hd)
    · -- no certified divisor: `π / 499 ≤ π`
      linarith


/-- `Capsule.arcBox` holds the sampled point. -/
private theorem Capsule.aux_arcBox_mem (p : ℕ) (step : Interval 𝕋) {s : ℝ}
    (hs : toReal step.inf ≤ s ∧ s ≤ toReal step.sup) (ctr : Interval (Vec 𝕋 2))
    (a₀ : Interval (Vec 𝕋 1)) (r : 𝕋) (i : ℕ) {c : Vec ℝ 2} (hc : c ∈ ctr.construct) {a : ℝ}
    (ha : (fun _ => a : Vec ℝ 1) ∈ a₀.construct) : -- --- CONCL ---
    (![c 0 + toReal r * Real.cos (a + (i : ℝ) * s), c 1 + toReal r * Real.sin (a + (i : ℝ) * s)] :
      Vec ℝ 2) ∈ (Capsule.arcBox p step ctr a₀ r i).construct := by -- --- PROOF ---
  -- the index and the step in their boxes
  have hi := intDown_le_intUp (𝕋 := 𝕋) (i : ℤ)
  have hidx : (fun _ => (i : ℝ) : Vec ℝ 1) ∈
      (⟨fun _ => intDown (i : ℤ), fun _ => intUp (i : ℤ)⟩ : Interval (Vec 𝕋 1)).construct :=
    fun _ => (show toReal (intDown (i : ℤ) : 𝕋) ≤ (i : ℝ) ∧
        (i : ℝ) ≤ toReal (intUp (i : ℤ) : 𝕋) from
      ⟨by simpa using hi.1, by simpa using hi.2⟩)
  have hstp : (fun _ => s : Vec ℝ 1) ∈
      (⟨fun _ => step.inf, fun _ => step.sup⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hs
  -- the angle, then its cosine and sine
  have hprod := Interval.times_outer
    (⟨fun _ => intDown (i : ℤ), fun _ => intUp (i : ℤ)⟩ : Interval (Vec 𝕋 1))
    ⟨fun _ => step.inf, fun _ => step.sup⟩ ⟨_, hidx, _, hstp, rfl⟩
  have hang := Interval.plus_outer a₀ _ (Set.add_mem_add ha hprod)
  have hcos := Interval.cos_outer p _ ⟨_, hang, rfl⟩
  have hsin := Interval.sin_outer p _ ⟨_, hang, rfl⟩
  -- the radius and the center's coordinates
  have hrad : (fun _ => toReal r : Vec ℝ 1) ∈
      (Interval.point fun _ => r : Interval (Vec 𝕋 1)).construct := fun _ => ⟨le_rfl, le_rfl⟩
  have hc0 : (fun _ => c 0 : Vec ℝ 1) ∈
      (⟨fun _ => ctr.inf 0, fun _ => ctr.sup 0⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hc 0
  have hc1 : (fun _ => c 1 : Vec ℝ 1) ∈
      (⟨fun _ => ctr.inf 1, fun _ => ctr.sup 1⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hc 1
  have hx := Interval.plus_outer _ _ (Set.add_mem_add hc0
    (Interval.times_outer _ _ ⟨_, hrad, _, hcos, rfl⟩))
  have hy := Interval.plus_outer _ _ (Set.add_mem_add hc1
    (Interval.times_outer _ _ ⟨_, hrad, _, hsin, rfl⟩))
  intro j
  fin_cases j
  · exact hx 0
  · exact hy 0


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vertices_outer (p k : ℕ) (C : Capsule 𝕋 2) (hr : 0 ≤ toReal C.r)
    (hnp : ¬ Real.Capsule.representsa_point C.nominal)
    (hI : C.I_error.construct = {0}) : -- --- CONCL ---
    ∀ B ∈ C.vertices p k, ∃ x ∈ B.construct, x ∈ frontier C.construct := by -- --- PROOF ---
  -- the box is the origin, so the set is the nominal capsule
  rw [Capsule.construct_eq_nominal hI]
  -- the float test answers `false`, or the capsule would be a point
  have hfl : C.representsa_point = false := by
    by_contra hne
    have ht : C.representsa_point = true := by simpa using hne
    exact hnp (Capsule.representsa_point_parts ht).2
  -- the box around the angle's two bounds
  set θB : Interval (Vec 𝕋 1) :=
    ⟨fun _ => Interval.atan2Lo p k (C.g 0) (C.g 1), fun _ => Interval.atan2Hi p k (C.g 0) (C.g 1)⟩
    with hθB
  -- the angle `θ`, `π/2`, the step and the two centers, in their boxes
  have hθ : (fun _ => Complex.arg ⟨toReal (C.g 0), toReal (C.g 1)⟩ : Vec ℝ 1) ∈
      θB.construct :=
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
  -- the step and the two centers
  have hstep := Capsule.aux_piStep_mem (𝕋 := 𝕋) p k
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
      (θB.minus
        ⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩).construct :=
    Interval.minus_outer _ _ (Set.sub_mem_sub hθ hq)
  have hpl : (fun _ => Complex.arg ⟨toReal (C.g 0), toReal (C.g 1)⟩ + Real.pi / 2 : Vec ℝ 1) ∈
      (θB.plus
        ⟨fun _ => acosDown p k zero, fun _ => acosUp p k zero⟩).construct :=
    Interval.plus_outer _ _ (Set.add_mem_add hθ hq)
  unfold Capsule.vertices
  rw [if_neg (by simp [hfl])]
  dsimp only
  intro B hB
  simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hB
  -- the sampled point is in the box, and is a vertex of the exact layer, so on the frontier
  rcases hB with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · refine ⟨_, Capsule.aux_arcBox_mem p (piStep p k) hstep _ _ C.r (i : ℕ) hc₁ hm, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inl (Or.inl ⟨i, rfl⟩)
  · refine ⟨_, Capsule.aux_arcBox_mem p (piStep p k) hstep _ _ C.r (i : ℕ) hc₂ hpl, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inl (Or.inr ⟨i, rfl⟩)
  · refine ⟨_, Capsule.aux_arcBox_mem p (piStep p k) hstep _ _ C.r 0 hc₁ hm, ?_⟩
    refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
    unfold Real.Capsule.vertices
    rw [if_neg hnp]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inr (by simp; exact ⟨rfl, rfl⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
