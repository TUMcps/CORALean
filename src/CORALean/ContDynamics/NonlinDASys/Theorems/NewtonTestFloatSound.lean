module

public import CORALean.ContDynamics.NonlinDASys.Operations.NewtonTestFloat
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.Global.ExistsUniqueZeroOfNewtonTest

@[expose] public section

/-!
# A passed float Newton test certifies a unique zero

If `G` encloses `g` and `J` its slopes over every box, and `newtonTestFloat G J c r` is `true`,
then `g` has exactly one zero in the closed sup-norm ball of radius `r` about `c`. Each check of
the test is a hypothesis of `existsUnique_zero_of_newtonTest`, read through the outward rounding:
the ball lies in the rounded box `c ± r`, the real `R J` in the interval product, `|1 - R J|` below
the magnitudes of its residual box, and `R g(c)` in `Interval.mtimes`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed test proves exactly one zero of `g` within `r` of `c`. -/
theorem NonlinDASys.newtonTestFloat_sound (g : Vec ℝ k → Vec ℝ k)
    (G : Interval (Vec 𝕋 k) → Interval (Vec 𝕋 k)) (J : Interval (Vec 𝕋 k) → Interval (Mat 𝕋 k k))
    (hG : ∀ X : Interval (Vec 𝕋 k), ∀ a ∈ X.construct, g a ∈ (G X).construct)
    (hJ : ∀ X : Interval (Vec 𝕋 k), ∀ a ∈ X.construct, ∀ a' ∈ X.construct,
      ∃ M ∈ (J X).construct, g a - g a' = M *ᵥ (a - a'))
    (c : Vec 𝕋 k) (r : 𝕋) (h : NonlinDASys.newtonTestFloat G J c r = true) : -- --- CONCL ---
    ∃! z, z ∈ Metric.closedBall (toRealVec c) (toReal r) ∧ g z = 0 := by -- --- PROOF ---
  unfold NonlinDASys.newtonTestFloat at h
  simp only [Interval.materialiseMat_eq] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨hr, hrows⟩ := h
  have hr0 : 0 ≤ toReal r := by
    have := toReal_le_of_le hr; rwa [toReal_zero] at this
  set R : Mat 𝕋 k k :=
    (Interval.point (Zonotope.basisInverse (J (Interval.point c)).centerMat)).inf
  set B : Interval (Vec 𝕋 k) := ⟨fun i => subDown (c i) r, fun i => addUp (c i) r⟩ with hB
  set E : Interval (Mat 𝕋 k k) := Interval.matMul (Interval.point R) (J B)
  set I : Mat 𝕋 k k := fun i j => if i = j then one else zero with hI
  set q : Vec 𝕋 k :=
    fun i => sumUp fun j => (Interval.matResidual E.inf E.sup I).magnitudeMat i j with hq
  -- the ball lies in the rounded box
  have hball : ∀ a ∈ Metric.closedBall (toRealVec c) (toReal r), a ∈ B.construct := by
    intro a ha i
    have hai : |a i - toRealVec c i| ≤ toReal r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at ha
      have := norm_le_pi_norm (a - toRealVec c) i
      rw [Real.norm_eq_abs, Pi.sub_apply] at this
      linarith
    have h1 := subDown_le_sub (c i) r
    have h3 := add_le_addUp (c i) r
    rw [abs_le] at hai
    constructor
    · show toReal (subDown (c i) r) ≤ a i
      unfold toRealVec at hai; linarith
    · show a i ≤ toReal (addUp (c i) r)
      unfold toRealVec at hai; linarith
  -- each slope's rows of `|1 - R J|` are below `q`
  have hrow : ∀ M ∈ (J B).construct, ∀ i,
      ∑ j, |(1 - toRealMat R * M) i j| ≤ toRealVec q i := by
    intro M hM i
    have hE : toRealMat R * M ∈ E.construct :=
      Interval.matMul_outer _ _ (Interval.mem_point R) hM
    have hres := Interval.sub_mem_matResidual (stored := I) (Interval.mem_mat_iff.mp hE)
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    have hij := Interval.mem_mat_iff.mp hres i j
    have hIij : toReal (I i j) = (1 : Mat ℝ k k) i j := by
      show toReal (if i = j then (one : 𝕋) else zero) = _
      rw [Matrix.one_apply]; split_ifs
      · exact SoundFloatArithmetic.toReal_one
      · exact SoundFloatArithmetic.toReal_zero
    rw [hIij] at hij
    have hsub : |(1 - toRealMat R * M) i j| = |(toRealMat R * M) i j - (1 : Mat ℝ k k) i j| := by
      rw [Matrix.sub_apply, abs_sub_comm]
    rw [hsub, Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hij.1 hij.2
  -- the residual at the center
  have hgc : ∀ i, |(toRealMat R *ᵥ g (toRealVec c)) i| ≤
      toReal ((Interval.mtimes R (G (Interval.point c))).magnitude i) := fun i =>
    Interval.abs_le_magnitude (Interval.mtimes_outer R _
      ⟨g (toRealVec c), hG _ _ (Interval.mem_point c), rfl⟩) i
  refine existsUnique_zero_of_newtonTest g (toRealVec c) hr0 (toRealMat R) (toRealVec q)
    (fun a ha a' ha' => ?_) (fun i => by
      have := toReal_lt_of_ltStrict (hrows i).1
      rwa [SoundFloatArithmetic.toReal_one] at this) (fun i => ?_)
  · obtain ⟨M, hM, hslope⟩ := hJ B a (hball a ha) a' (hball a' ha')
    exact ⟨M, hslope, hrow M hM⟩
  · have hle := toReal_le_of_le (hrows i).2
    have h1 := add_le_addUp (mulUp (q i) r) ((Interval.mtimes R (G (Interval.point c))).magnitude i)
    have h2 := mul_le_mulUp (q i) r
    have h3 := hgc i
    show toReal (q i) * toReal r + _ ≤ _
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
