module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.HessRemainderMem
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The remainder at a shifted Hessian

The remainder of the expansion about `(x✱, u✱)` less its quadratic part at `Hp` lies in the
`hessRemainder` of the model whose Hessian boxes are shifted by `-Hp`: the Hessians of the
expansion less `Hp` are in the shifted boxes, and `hessRemainder_mem` applies.

## Inputs
* `fm` – float Hessian model
* `sys` – system
* `Hp` – Hessian matrices to subtract
* `A` – state matrix
* `B` – input matrix
* `xs` – state expansion point
* `us` – input expansion point
* `X` – state box
* `U'` – input box
* `x` – state value in the state box
* `u` – input value in the input box

## Hypotheses
* `h` – the model encloses the system
* `hxs` – the state point is in `X`
* `hus` – the input point is in `U'`
* `hx` – the state is in `X`
* `hu` – the input is in `U'`

## Conclusion
* the remainder less its quadratic part at `Hp` is in the shifted model's `hessRemainder`
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

/-- A matrix's negation, stored entrywise, is a point interval at the negated real one. -/
private theorem aux_hsr_neg_mat {k l : ℕ} (A : Mat 𝕋 k l) : -- --- CONCL ---
    -Scalar.toRealMat A ∈
      (Interval.point (α := Mat 𝕋 k l) (-A)).toSet := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 k l) (-A)
  have he : (RealImage.realImage (α := Mat 𝕋 k l) (-A) : Mat ℝ k l)
      = -Scalar.toRealMat A := by
    funext i j
    exact toReal_neg (A i j)
  rwa [he] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the model's Hessian boxes differ from `Hp` by, over a box: the remainder of the expansion
about `(x✱, u✱)` less its quadratic part at `Hp` lies in the shifted model's `hessRemainder`. -/
theorem NonlinearSys.FloatHessModel.Encloses.hessShiftRemainder_mem
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (Hp : Fin n → Mat 𝕋 (n + m) (n + m)) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n)
    (us : Vec 𝕋 m) {X : Interval (Vec 𝕋 n)} {U' : Interval (Vec 𝕋 m)}
    (hxs : toRealVec xs ∈ X.toSet) (hus : toRealVec us ∈ U'.toSet) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ X.toSet) (hu : u ∈ U'.toSet) : -- --- CONCL ---
    sys.f x u - (sys.f (toRealVec xs) (toRealVec us) + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      + Scalar.toRealMat B *ᵥ (u - toRealVec us)) - (fun i => Fin.append (x - toRealVec xs)
        (u - toRealVec us) ⬝ᵥ (Scalar.toRealMat (Hp i) *ᵥ Fin.append (x - toRealVec xs)
          (u - toRealVec us)) / 2) ∈
      (({ fm with hess := fun X U i => Interval.matPlus (fm.hess X U i) (Interval.point (-Hp i)) }
        : NonlinearSys.FloatHessModel 𝕋 n m).hessRemainder A B xs us X U').zonotope.toSet
    := by -- --- PROOF ---
  set fmS : NonlinearSys.FloatHessModel 𝕋 n m :=
    { fm with hess := fun X U i => Interval.matPlus (fm.hess X U i) (Interval.point (-Hp i)) }
    with hfmS
  -- the expansion about `(x✱, u✱)` over the boxes
  obtain ⟨Jx, hJx, Ju, hJu, H, hH, htay⟩ := h.taylor_mem X U' xs us hxs hus x hx u hu
  set dz := Fin.append (x - toRealVec xs) (u - toRealVec us)
  -- the remainder less the quadratic part at `Hp`, in terms of `H - Hp`
  have hrem : sys.f x u - (sys.f (toRealVec xs) (toRealVec us)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec us))
      - (fun i => dz ⬝ᵥ (Scalar.toRealMat (Hp i) *ᵥ dz) / 2)
      = ((Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
        + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec us))
        + fun i => dz ⬝ᵥ ((H i - Scalar.toRealMat (Hp i)) *ᵥ dz) / 2 := by
    have hf : sys.f x u = sys.f (toRealVec xs) (toRealVec us)
        + (Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec us)
          + fun i => dz ⬝ᵥ (H i *ᵥ dz) / 2) := by
      rw [← htay]; abel
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hf]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.sub_mulVec, dotProduct_sub]
    ring
  rw [hrem]
  -- the Hessians less `Hp` are in the shifted boxes
  have hH' : ∀ i, H i - Scalar.toRealMat (Hp i) ∈
      (fmS.hess X U' i).toSet := fun i => by
    have := Interval.matPlus_outer _ _ (hH i) (aux_hsr_neg_mat (Hp i))
    rwa [← sub_eq_add_neg] at this
  exact Interval.zonotope_contains _
    (fmS.hessRemainder_mem A B xs us X U' hJx hJu hH' hx hu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
