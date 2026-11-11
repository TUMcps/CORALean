module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessCenterTableEq
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessShiftRemainderMem
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeEvenContains
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapMixedOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `abstrErrPolyAdaptiveFloat` holds the remainder, less the static error

At a state `x = x✱ + a + d` of `Rmax` (`a` a point of the start set, `d` a difference the step
spans) and an input of `U`, the field less its affine part at the linearization point and less the
static error `½ zᵀ H✱ z` at `z = (a, u - u✱)` lies in `VerrorDyn`. The expansion about `x✱` splits
the quadratic part at `z + (d, 0)` into `½ zᵀ H✱ z` and the three products that carry `d`, which are
`quadMapMixed` and `quadMap` of the sets `Zdelta` and `Zdiff` hold; the rest is the remainder of the
model whose Hessian boxes are shifted by `-H✱` (`hessShiftRemainder_mem`). The reductions only
enlarge.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `A` – state matrix
* `B` – input matrix
* `xs` – state expansion point
* `Rmax` – state set
* `Zdelta` – zonotope of the start set with the input
* `Rdiff` – differences
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision
* `x` – state in `Rmax`
* `a` – the state's start part
* `d` – the state's difference
* `u` – input in `U`

## Hypotheses
* `h` – model encloses system
* `hx` – state in `Rmax`
* `hxd` – the state less `x✱` is `a + d`
* `ha` – the start part with the input is in `Zdelta`
* `hd` – the difference is in `Rdiff`
* `hu` – input in `U`

## Conclusion
* the remainder less the static error lies in `VerrorDyn`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box joined with a point holds the box and the point. -/
private theorem aux_apa_mem_hull {k : ℕ} (I : Interval (Vec 𝕋 k))
    (v : Vec 𝕋 k) : -- --- CONCL ---
    I.toSet ⊆ (⟨fun i => minimum (I.inf i) (v i), fun i => maximum (I.sup i) (v i)⟩ :
      Interval (Vec 𝕋 k)).toSet ∧ toRealVec v ∈ (⟨fun i => minimum (I.inf i) (v i),
        fun i => maximum (I.sup i) (v i)⟩ : Interval (Vec 𝕋 k)).toSet := by -- --- PROOF ---
  refine ⟨fun y hy i => ?_, fun i => ?_⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ y i ∧ y i ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_of_left_le (hy i).1, le_max_of_le_left (hy i).2⟩
  · show toReal (minimum (I.inf i) (v i)) ≤ toReal (v i)
      ∧ toReal (v i) ≤ toReal (maximum (I.sup i) (v i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- The blocks of an appended vector add. -/
private theorem aux_apa_append_add {k l : ℕ} (a b : Vec ℝ k) (c d : Vec ℝ l) :
    Fin.append (a + b) (c + d) = Fin.append a c + Fin.append b d := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- The remainder at a state `x✱ + a + d` of `Rmax`, less the static error at `(a, u - u✱)`, lies
in `abstrErrPolyAdaptiveFloat`. -/
theorem NonlinearSys.FloatHessModel.Encloses.abstrErrPolyAdaptiveFloat_mem
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Rmax : Zonotope (Vec 𝕋 n))
    (Zdelta : Zonotope (Vec 𝕋 (n + m))) (Rdiff : PolyZonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (redFactor : 𝕋) (p : ℕ) {x a d : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ Rmax.toSet) (hxd : x - toRealVec xs = a + d)
    (ha : Fin.append a (u - toRealVec U.c) ∈ Zdelta.toSet) (hd : d ∈ Rdiff.toSet)
    (hu : u ∈ U.toSet) : -- --- CONCL ---
    sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      + Scalar.toRealMat B *ᵥ (u - toRealVec U.c))
      - (fun i => Fin.append a (u - toRealVec U.c) ⬝ᵥ (Scalar.toRealMat
        ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ
          Fin.append a (u - toRealVec U.c)) / 2) ∈
      (fm.abstrErrPolyAdaptiveFloat A B xs Rmax Zdelta Rdiff U redFactor
        p).toSet := by -- --- PROOF ---
  set Hc : Fin n → Mat 𝕋 (n + m) (n + m) :=
    fun i => (fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat with hHc
  unfold NonlinearSys.FloatHessModel.abstrErrPolyAdaptiveFloat
  dsimp only
  simp only [NonlinearSys.FloatHessModel.hessCenterTable_eq]
  rw [Zonotope.materialise_eq]
  refine Zonotope.reduceAdaptive_outer _ _ _ ?_
  -- the boxes the Hessian is read over
  have hxsX := (aux_apa_mem_hull Rmax.interval xs).2
  have husU := (aux_apa_mem_hull U.interval U.c).2
  have hxX := (aux_apa_mem_hull Rmax.interval xs).1 (Zonotope.interval_contains Rmax hx)
  have huU := (aux_apa_mem_hull U.interval U.c).1 (Zonotope.interval_contains U hu)
  have hrest := h.hessShiftRemainder_mem Hc A B xs U.c hxsX husU hxX huU
  -- the quadratic part at `z + (d, 0)` splits into the three products
  set μ := u - toRealVec U.c with hμ
  set a' : Vec ℝ (n + m) := Fin.append a μ with ha'
  set b' : Vec ℝ (n + m) := Fin.append d (0 : Vec ℝ m) with hb'
  have hdz : Fin.append (x - toRealVec xs) μ = a' + b' := by
    rw [hxd]
    have := aux_apa_append_add a d μ (0 : Vec ℝ m)
    rwa [add_zero] at this
  -- the sets the three products read
  have hPδ : a' ∈ (Zdelta.ofIndep).toSet := Zonotope.ofIndep_outer _ ha
  -- the differences, boxed and reduced, with a zero input, are in the Cartesian product
  have hdRed : d ∈
      (Rdiff.zonotopeEven.materialise.reduceAdaptive (sqrtUp p redFactor) p).toSet := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.reduceAdaptive_outer _ _ _ (PolyZonotope.zonotopeEven_contains _ hd)
  have hb : b' ∈ ((Rdiff.zonotopeEven.materialise.reduceAdaptive (sqrtUp p redFactor) p).cartProd
      (Recenter.recenter U)).toSet := by
    rw [Zonotope.cartProd_exact]
    exact ⟨(d, 0), ⟨hdRed, Recenter.zero_mem_recenter U⟩, rfl⟩
  have hPd := Zonotope.ofIndep_outer _ hb
  set Q : Fin n → Mat 𝕋 (n + m) (n + m) :=
    fun i a b => half ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat a b)
    with hQdef
  -- `Q` is `H✱` halved, exactly
  have hQ : ∀ i, toRealMat (Q i) = (1 / 2 : ℝ) • Scalar.toRealMat (Hc i) := by
    intro i
    funext a b
    rw [Matrix.smul_apply, Scalar.toRealMat_apply]
    show toReal (half ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat a b))
      = 1 / 2 * toReal (Hc i a b)
    rw [toReal_half]
    change toReal (Hc i a b) / 2 = 1 / 2 * toReal (Hc i a b)
    ring
  have m1 := PolyZonotope.quadMapMixed_outer Q Zdelta.ofIndep _ ⟨(a', b'), ⟨hPδ, hPd⟩, rfl⟩
  have m2 := PolyZonotope.quadMapMixed_outer Q _ Zdelta.ofIndep ⟨(b', a'), ⟨hPd, hPδ⟩, rfl⟩
  have m3 := PolyZonotope.quadMap_outer Q _ ⟨b', hPd, rfl⟩
  -- the remainder is the three products and the shifted model's remainder
  rw [hdz] at hrest
  -- the field less its affine part and the static error splits into those pieces
  have heq : sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ μ) - (fun i => a' ⬝ᵥ
          (Scalar.toRealMat (Hc i) *ᵥ a') / 2)
      = ((Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k)) a' b'
          + Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k)) b' a')
          + Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) b')
        + (sys.f x u - (sys.f (toRealVec xs) (toRealVec U.c)
          + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ μ)
          - (fun i => (a' + b') ⬝ᵥ (Scalar.toRealMat (Hc i) *ᵥ (a' + b')) / 2)) := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Real.PolyZonotope.quadBilin, Real.PolyZonotope.quadEval,
      LinearMap.mk₂_apply, hQ k, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  rw [heq]
  -- the three products are in the reduced sets
  refine Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add ?_ hrest)
  rw [Zonotope.materialise_eq]
  refine PolyZonotope.zonotopeEven_contains _ ?_
  refine Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := PolyZonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add ?_ ?_)) ?_)
  · rw [PolyZonotope.materialise_eq]
    exact m1
  · rw [PolyZonotope.materialise_eq]
    exact m2
  · rw [PolyZonotope.materialise_eq]
    exact m3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
