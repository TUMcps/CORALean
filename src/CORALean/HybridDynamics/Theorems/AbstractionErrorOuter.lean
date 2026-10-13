import CORALean.HybridDynamics.Operations.AbstractionError
import CORALean.HybridDynamics.Theorems.AbstractionErrorDecomp
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubExpTaylorMemExpRemainderInterval
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.SumTermsMem

/-!
# The abstraction error encloses the difference of a run and the constant flow

[1, Eq. 13] as CORA computes it (`GuardMap.abstractionError`): for `t ∈ [0, tmax]`, `η ≥ 1`,
`x₀ ∈ R₀` and a measurable input `u` with values in `U`, the run
`e^{At}x₀ + ∫₀ᵗ e^{A(t−s)}u(s) ds` of `ẋ = Ax + u` differs from the state-dependent constant
flow `x₀ + (Ax₀ + b)t` of [1, Eq. 3], `b = Θ(th)ξ + Γ*(th)u_c` of [1, Prop. 1] at the centres
`ξ` of `R₀` and `u_c` of `U`, by a point of the set.

Both Taylor series are cut at `η`. `GuardMap.abstractionError_decomp` splits the difference
into `t(v₁ + v₂ + v₃) + R(t)x₀ + ρ`, the input's orders averages `wᵢ ∈ U`, and `wᵢ − u_c ∈ U ⊖ u_c`;
the remainders `R(τ) = e^{Aτ} − ∑ᵢ₌₀^η (Aτ)ⁱ/i!` lie entrywise in `[−W, W]` for `τ ≤ tmax`, so
`R(t)x₀ ∈ Ê R₀` and the integral of `R(τ)u(t − τ)` in `Ê tmax U`, a convex set holding `0`.
`η ≥ 1` because the flow's own `Ax₀t` is the Taylor series' first order. Any `th`: it only
moves `b`, and the error set with it.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point matrix scaled by a point of `[a, b]` lies in the entrywise product
`[lo, hi] * [a, b]`. -/
theorem aux_absErr_smul_mem {lo hi M : Mat ℝ n n} {a b s : ℝ}
    (hM : ∀ j k, lo j k ≤ M j k ∧ M j k ≤ hi j k) (hs : a ≤ s ∧ s ≤ b) :
    s • M ∈ (⟨Matrix.of fun j k => Interval.mulLo (lo j k) (hi j k) a b,
      Matrix.of fun j k => Interval.mulHi (lo j k) (hi j k) a b⟩ :
        Interval (Mat ℝ n n)).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have h := Interval.mul_between_corners (hM j k).1 (hM j k).2 hs.1 hs.2
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm s]
  exact h

/-- A point of the interval matrix applied to a point of the zonotope. -/
theorem aux_absErr_mulVec_mem {IM : Interval (Mat ℝ n n)} {Z : Zonotope (Vec ℝ n)}
    {M : Mat ℝ n n} {v : Vec ℝ n} (hM : M ∈ IM.construct) (hv : v ∈ Z.construct) :
    M *ᵥ v ∈ (Zonotope.mtimesIntervalMat IM Z).construct :=
  Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ hv))


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13]: `x(t) − y(t) ∈ E` for a run from `x₀ ∈ R₀` with inputs in `U`,
`t ∈ [0, tmax]`, `η ≥ 1`. -/
theorem GuardMap.abstractionError_outer (A : Mat ℝ n n) (U R₀ : Zonotope (Vec ℝ n)) (th : ℝ)
    {tmax t : ℝ} {η : ℕ} (hη : 1 ≤ η) (ht : t ∈ Set.Icc 0 tmax) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ R₀.construct) {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ U.construct)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t))) :
    exp (t • A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
        - GuardMap.sdcFlow A (GuardMap.sdcInput A U.c th η R₀.c) x₀ t
      ∈ (GuardMap.abstractionError A U R₀ th tmax η).construct := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
  -- `W` bounds every remainder on `[0, tmax]`, and `Ê tmax U` holds `tmax M v`, `|M| ≤ W`
  set W : Mat ℝ n n := fun j k' => |MatExp.expRemainderMat A tmax (k + 1) j k'| with hWdef
  have hW : ∀ τ ∈ Set.Icc 0 tmax, ∀ j l,
      |(exp (τ • A) - MatExp.expTaylor (τ • A) (k + 1)) j l| ≤ W j l := fun τ hτ j l =>
    le_trans (le_trans (MatExp.exp_sub_expTaylor_mem_expRemainderInterval A hτ.1 (k + 1) j l)
      (MatExp.expRemainderMat_mono A hτ.1 hτ.2 (k + 1) j l)) (le_abs_self _)
  set IM : Interval (Mat ℝ n n) := ⟨Matrix.of fun j k => Interval.mulLo (-W j k) (W j k) tmax tmax,
    Matrix.of fun j k => Interval.mulHi (-W j k) (W j k) tmax tmax⟩ with hIM
  have hS : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ W j l) → ∀ v ∈ U.construct,
      tmax • (M *ᵥ v) ∈ (Zonotope.mtimesIntervalMat IM U).construct := fun M hM v hv => by
    rw [← Matrix.smul_mulVec]
    exact aux_absErr_mulVec_mem (aux_absErr_smul_mem (fun j l => abs_le.mp (hM j l))
      ⟨le_rfl, le_rfl⟩) hv
  have hS0 : (0 : Vec ℝ n) ∈ (Zonotope.mtimesIntervalMat IM U).construct := by
    simpa using hS 0 (fun j l => by simp [hWdef]) U.c (Zonotope.centre_mem_construct U)
  obtain ⟨w, hw, ρ, hρ, hid⟩ := GuardMap.abstractionError_decomp A
    (Zonotope.convex_construct U) (Zonotope.isClosed_construct U)
    (Zonotope.isBounded_construct U) ⟨U.c, Zonotope.centre_mem_construct U⟩
    (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
    (Zonotope.isBounded_construct _) hS0 U.c R₀.c th ht W hW hS x₀ hu hmeas
  -- the decomposition's parts, named as the sets of `aux_abstractionError` read them
  set ξ := R₀.c
  set uc := U.c
  set Mf : ℕ → Mat ℝ n n := fun m => ((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1) with hMf
  -- the three parts of `τ(err₁ ⊕ err₂ ⊕ err₃)`, before the factor `t`
  set v1 : Vec ℝ n := ∑ m ∈ Finset.range k, (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2)) *ᵥ
    (t ^ (m + 1) • x₀ + (-(th ^ (m + 1))) • ξ) with hv1
  set v2 : Vec ℝ n := ∑ m ∈ Finset.range (k + 1), ((t ^ (m + 1) - th ^ (m + 1)) • Mf m) *ᵥ uc
    with hv2
  set v3 : Vec ℝ n := (w 0 - uc) + ∑ m ∈ Finset.range (k + 1), (t ^ (m + 1) • Mf m) *ᵥ
    (w (m + 1) - uc) with hv3
  rw [hid]
  -- the memberships, part by part
  simp only [GuardMap.abstractionError, Nat.add_sub_cancel]
  rw [← Zonotope.plus_exact, ← Zonotope.plus_exact]
  have htpow : ∀ m : ℕ, 0 ≤ t ^ m ∧ t ^ m ≤ tmax ^ m := fun m =>
    ⟨pow_nonneg ht.1 m, pow_le_pow_left₀ ht.1 ht.2 m⟩
  have hone : ∀ j k : Fin n, (1 : Mat ℝ n n) j k ≤ (1 : Mat ℝ n n) j k ∧
      (1 : Mat ℝ n n) j k ≤ (1 : Mat ℝ n n) j k := fun _ _ => ⟨le_rfl, le_rfl⟩
  have hself : ∀ (M : Mat ℝ n n) (j k : Fin n), M j k ≤ M j k ∧ M j k ≤ M j k :=
    fun _ _ _ => ⟨le_rfl, le_rfl⟩
  refine Set.add_mem_add (Set.add_mem_add ?_ ?_) hρ
  · -- `t(v₁ + v₂ + v₃) = (t I)(v₁ + v₂ + v₃)`
    have hV : v1 + v2 + v3 ∈ (((Zonotope.sumTerms (fun m =>
        Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2))
          ((Zonotope.mtimesIntervalMat ⟨Matrix.of fun j k => Interval.mulLo
              ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) 0 (tmax ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) 0
              (tmax ^ (m + 1))⟩ R₀).plus (Zonotope.ofPoint (-(th ^ (m + 1)) • ξ)))) k).plus
        (Zonotope.sumTerms (fun m => Zonotope.mtimesIntervalMat
          ⟨Matrix.of fun j k => Interval.mulLo (Mf m j k) (Mf m j k) (-(th ^ (m + 1)))
              (tmax ^ (m + 1) - th ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi (Mf m j k) (Mf m j k) (-(th ^ (m + 1)))
              (tmax ^ (m + 1) - th ^ (m + 1))⟩ (Zonotope.ofPoint uc)) (k + 1))).plus
        (U.recentre.plus (Zonotope.sumTerms (fun m => Zonotope.mtimesIntervalMat
          ⟨Matrix.of fun j k => Interval.mulLo (Mf m j k) (Mf m j k) 0 (tmax ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi (Mf m j k) (Mf m j k) 0 (tmax ^ (m + 1))⟩
          U.recentre) (k + 1)))).construct := by
      rw [← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.plus_exact]
      refine Set.add_mem_add (Set.add_mem_add ?_ ?_) (Set.add_mem_add
        (Zonotope.sub_centre_mem_recentre (hw 0)) ?_)
      · -- `err₁`: `(Aⁱ/i!)(tⁱ⁻¹x₀ − thⁱ⁻¹ξ)`, `tⁱ⁻¹ ∈ [0, tmaxⁱ⁻¹]`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        rw [← Zonotope.mtimes_exact, ← Zonotope.plus_exact]
        refine ⟨_, Set.add_mem_add ?_ (Zonotope.mem_ofPoint _), rfl⟩
        rw [show t ^ (m + 1) • x₀ = (t ^ (m + 1) • (1 : Mat ℝ n n)) *ᵥ x₀ by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]]
        exact aux_absErr_mulVec_mem (aux_absErr_smul_mem hone (htpow (m + 1))) hx₀
      · -- `err₂`: `((tⁱ − thⁱ) Aⁱ/(i+1)!) u_c`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        refine aux_absErr_mulVec_mem (aux_absErr_smul_mem (hself (Mf m)) ⟨?_, ?_⟩)
          (Zonotope.mem_ofPoint _)
        · linarith [(htpow (m + 1)).1]
        · linarith [(htpow (m + 1)).2]
      · -- `err₃`: `(tⁱ Aⁱ/(i+1)!)(wᵢ − u_c)`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        exact aux_absErr_mulVec_mem (aux_absErr_smul_mem (hself (Mf m)) (htpow (m + 1)))
          (Zonotope.sub_centre_mem_recentre (hw (m + 1)))
    rw [show t • (v1 + v2 + v3) = (t • (1 : Mat ℝ n n)) *ᵥ (v1 + v2 + v3) by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]]
    exact aux_absErr_mulVec_mem (aux_absErr_smul_mem hone ⟨ht.1, by simpa using ht.2⟩) hV
  · -- `R(t) ∈ Ê`
    have hRb := MatExp.exp_sub_expTaylor_mem_expRemainderInterval A ht.1 (k + 1)
    refine aux_absErr_mulVec_mem (Interval.mem_mat_iff.mpr fun j k' => ?_) hx₀
    have h1 := le_trans (hRb j k') (MatExp.expRemainderMat_mono A ht.1 ht.2 (k + 1) j k')
    exact abs_le.mp (le_trans h1 (le_abs_self _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
