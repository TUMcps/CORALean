module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessRemainderMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessShiftRemainderMem
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `abstrErrAdaptiveFloat` holds the remainder over `Rmax`

At a state of `Rmax` and an input of `U`, `f` less its affine part at the linearization point lies
in `abstrErrAdaptiveFloat` at either tensor order. The box of `Rmax` joined with `x✱` holds the
segment from `x✱` the Lagrange form reads. At order `2` the expansion of `Encloses.taylor_mem` is
bounded as in `hessRemainder_abstractionError`. At order `3` it splits into `½ zᵀ H✱ z`, in
`quadMap(Z, ½ H✱)` since `z = (x - x✱, u - u✱) ∈ Z`, and the remainder of the model whose Hessian
boxes are shifted by `-H✱`. The reductions only enlarge.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `κ` – tensor order
* `A` – state matrix
* `B` – input matrix
* `xs` – state expansion point
* `Rmax` – state set
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision
* `x` – state in `Rmax`
* `u` – input in `U`

## Hypotheses
* `h` – model encloses system
* `hx` – state in `Rmax`
* `hu` – input in `U`

## Conclusion
* the remainder at the state and input lies in the abstraction error
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box joined with a point holds the box and the point. -/
private theorem aux_aea_mem_hull {k : ℕ} (I : Interval (Vec 𝕋 k))
    (v : Vec 𝕋 k) : -- --- CONCL ---
    I.toSet ⊆ (step_hullPoint I v).toSet ∧
      toRealVec v ∈ (step_hullPoint I v).toSet := by -- --- PROOF ---
  refine ⟨fun y hy i => ?_, fun i => ?_⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ y i ∧ y i ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_of_left_le (hy i).1, le_max_of_le_left (hy i).2⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ toReal (v i)
      ∧ toReal (v i) ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- The generator-free zonotope at `v` holds `v`. -/
private theorem aux_aea_mem_pt {k : ℕ} (v : Vec 𝕋 k) : -- --- CONCL ---
    toRealVec v ∈ (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
      Zonotope (Vec 𝕋 k)).toSet := by -- --- PROOF ---
  refine ⟨toRealVec v, Zonotope.mem_nominalSet_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0,
    fun i => by simp [toRealVec]⟩, 0, fun i => ?_, add_zero _⟩
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ k) i ∧ (0 : Vec ℝ k) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order, the remainder of the linearization at `A`, `B`,
`(x✱, center(U))` at a state of `Rmax` and an input of `U` lies in `abstrErrAdaptiveFloat`. -/
theorem NonlinearSys.FloatHessModel.Encloses.abstrErrAdaptiveFloat_mem
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (κ : ℕ) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Rmax : Zonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (redFactor : 𝕋) (p : ℕ) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ Rmax.toSet) (hu : u ∈ U.toSet) : -- --- CONCL ---
    sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      + Scalar.toRealMat B *ᵥ (u - toRealVec U.c)) ∈
      (fm.abstrErrAdaptiveFloat κ A B xs Rmax U redFactor p).toSet := by -- --- PROOF ---
  set X := step_hullPoint Rmax.interval xs
  set U' := step_hullPoint U.interval U.c
  have hxX : x ∈ X.toSet := (aux_aea_mem_hull _ xs).1 (Zonotope.interval_contains Rmax hx)
  have huU : u ∈ U'.toSet := (aux_aea_mem_hull _ U.c).1 (Zonotope.interval_contains U hu)
  -- the expansion about `(x✱, u✱)` over the joined boxes
  obtain ⟨Jx, hJx, Ju, hJu, H, hH, htay⟩ := h.taylor_mem X U' xs U.c (aux_aea_mem_hull _ xs).2
    (aux_aea_mem_hull _ U.c).2 x hxX u huU
  set dz := Fin.append (x - toRealVec xs) (u - toRealVec U.c)
  have hrem : ∀ H' : Fin n → Mat ℝ (n + m) (n + m),
      sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c))
      = (fun i => dz ⬝ᵥ (H' i *ᵥ dz) / 2) + (((Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
        + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec U.c))
        + fun i => dz ⬝ᵥ ((H i - H' i) *ᵥ dz) / 2) := by
    intro H'
    have hf : sys.f x u = sys.f (toRealVec xs) (toRealVec U.c)
        + (Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec U.c)
          + fun i => dz ⬝ᵥ (H i *ᵥ dz) / 2) := by
      rw [← htay]; abel
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hf]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.sub_mulVec, dotProduct_sub]
    ring
  -- the two tensor orders
  unfold NonlinearSys.FloatHessModel.abstrErrAdaptiveFloat
  split_ifs with hκ
  · -- tensor order 3: the quadratic map at `H✱`, and the shifted model's remainder
    set Hp := fun i => (fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat
    refine Zonotope.reduceAdaptive_outer _ _ _ ?_
    rw [hrem fun i => Scalar.toRealMat (Hp i)]
    -- `z ∈ Z`, and `quadMap` at `½ H✱`
    have hsec : (fun i => dz ⬝ᵥ (Scalar.toRealMat (Hp i) *ᵥ dz) / 2) ∈
        (Zonotope.quadMap (fun i a b => half (Hp i a b)) ((((Rmax ⊞ (⟨0, -xs, fun j => j.elim0,
          ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))).reduceAdaptive
            (sqrtUp p redFactor) p).cartProd (Recenter.recenter U)))).toSet := by
      have hz : dz ∈ ((((Rmax ⊞ (⟨0, -xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
          Zonotope (Vec 𝕋 n))).reduceAdaptive (sqrtUp p redFactor) p).cartProd
            (Recenter.recenter U)).toSet) := by
        rw [Zonotope.cartProd_exact]
        refine ⟨(x - toRealVec xs, u - toRealVec U.c), ⟨?_, ?_⟩, rfl⟩
        · refine Zonotope.reduceAdaptive_outer _ _ _ ?_
          have hp := aux_aea_mem_pt (-xs)
          have hneg : toRealVec (-xs) = -toRealVec xs := funext fun i => toReal_neg (xs i)
          rw [hneg] at hp
          have := Plus.plus_outer Rmax _ (Set.add_mem_add hx hp)
          rwa [← sub_eq_add_neg] at this
        · exact Zonotope.sub_center_mem_recenter hu
      -- `quadMap`'s guarantee at `z`, its matrices halved exactly
      have hq := Zonotope.quadMap_outer (fun i a b => half (Hp i a b)) _ (Set.mem_image_of_mem _ hz)
      convert hq using 1
      funext i
      simp only [Real.PolyZonotope.quadEval]
      have hhalf : (toRealMat fun a b => half (Hp i a b)) =
          (1 / 2 : ℝ) • Scalar.toRealMat (Hp i) := by
        funext a b
        rw [Matrix.smul_apply, Scalar.toRealMat_apply, toRealMat, toReal_half, smul_eq_mul]
        change toReal (Hp i a b) / 2 = 1 / 2 * toReal (Hp i a b)
        ring
      rw [hhalf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      ring
    -- the rest: the model with its Hessian boxes shifted by `-H✱`
    have hrest : ((Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
        + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec U.c))
        + (fun i => dz ⬝ᵥ ((H i - Scalar.toRealMat (Hp i)) *ᵥ dz) / 2) ∈
        (((fm.step_hessShift Hp).hessRemainder A B xs U.c X U').zonotope).toSet := by
      have h3 := h.hessShiftRemainder_mem Hp A B xs U.c (aux_aea_mem_hull _ xs).2
        (aux_aea_mem_hull _ U.c).2 hxX huU
      rw [hrem fun i => Scalar.toRealMat (Hp i), add_sub_cancel_left] at h3
      exact h3
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hsec hrest)
  · -- tensor order 2: the remainder at the Hessian box
    refine Interval.zonotope_contains _ ?_
    rw [hrem fun _ => 0]
    have h0 : (fun i => dz ⬝ᵥ ((0 : Mat ℝ (n + m) (n + m)) *ᵥ dz) / 2 : Vec ℝ n) = 0 := by
      funext i; simp
    rw [h0, zero_add]
    simpa using fm.hessRemainder_mem A B xs U.c X U' hJx hJu hH hxX huU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
