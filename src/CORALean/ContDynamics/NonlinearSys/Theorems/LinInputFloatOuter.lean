module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinInputFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.SlopeRemainderAbstractionError
public import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem

@[expose] public section

/-!
# `linInputFloat` holds every input the linearized system needs

The deviation-coordinate counterpart of `linInput_outer`: for a state `x` in the
certified box and an input `u ∈ U`, `f(x,u) - A(x - x✱)` is in `linInputFloat`,
so `δ = x - x✱` solves `δ̇ = A δ + ũ` with `ũ` there. Split as `f(x✱,u✱)`, then
`B(u - u✱)`, then the remainder `slopeRemainder_abstractionError` places, each in
its own summand.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys`, `X` holds `x` and `x✱`, and `U'` holds `U` and its
centre, `f(x, u) - A(x - x✱)` lies in `linInputFloat`. -/
theorem NonlinearSys.FloatModel.Encloses.linInputFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {xs : Vec 𝕋 n} {X : Interval (Vec 𝕋 n)}
    {U : Zonotope (Vec 𝕋 m)} {U' : Interval (Vec 𝕋 m)} (hxs : toRealVec xs ∈ X.construct)
    (hU : U.construct ⊆ U'.construct) (hus : toRealVec U.c ∈ U'.construct)
    {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ X.construct) (hu : u ∈ U.construct) :
    sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      ∈ (fm.linInputFloat A B xs X U U').construct := by -- --- PROOF ---
  set us := toRealVec U.c with hus_def
  have hL := (h.slopeRemainder_abstractionError A B hxs hus).encloses x hx u (hU hu)
  -- `f(x✱, u✱)`, from the model at the point
  have hf₀ : sys.f (toRealVec xs) us ∈ (fm.f (Interval.point xs) (Interval.point U.c)).construct :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  -- `B(u - u✱)`, `u - u✱` being in `U`'s recentred set
  have hBu : Scalar.toRealMat B *ᵥ (u - us) ∈ construct
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B
      (Recentre.recentre U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B _
      (Set.mem_biUnion (Set.mem_singleton _)
      (Set.mem_image_of_mem _ (Zonotope.sub_centre_mem_recentre hu)))
  have hsplit : sys.f x u - Scalar.toRealMat A *ᵥ (x - toRealVec xs)
      = (sys.f (toRealVec xs) us + Scalar.toRealMat B *ᵥ (u - us))
        + (sys.f x u - (sys.f (toRealVec xs) us + Scalar.toRealMat A *ᵥ (x - toRealVec xs)
          + Scalar.toRealMat B *ᵥ (u - us))) := by abel
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add
    (Interval.zonotope_contains _ hf₀) hBu)) (Interval.zonotope_contains _ hL))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
