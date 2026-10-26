module

public import CORALean.ContDynamics.NonlinDASys.Operations.OutputSetLinearFloat
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.Global.JacobianMatAffine

@[expose] public section

/-!
# The float linear output set holds the output of every state, algebraic variable and input

For an affine output `h(x, y, u) = c + M_x x + M_y y + M_u u` and a float model enclosing it, the
output of every `x ∈ R`, `y ∈ R_y` and `u ∈ U` lies in `outputSetLinearFloat`, as in
`NonlinDASys.outputSetLinear_outer`: the first-order expansion at the centers is exact, the value
`h(p)` lies in the model's box and converted zonotope, each Jacobian (the matrix of its block) in
the model's box, each shifted set holds its deviation, and the products and sums are enclosed.

## Inputs
* `sys` – system
* `om` – float model of the output equation
* `c` – output offset
* `M_x` – output matrix in the state
* `M_y` – output matrix in the algebraic variable
* `M_u` – output matrix in the input
* `p_x` – float state center
* `p_y` – float algebraic center
* `p_u` – float input center
* `R` – float state set
* `R_y` – float algebraic set
* `U` – float input set
* `x` – state
* `y` – algebraic variable
* `u` – input at the point

## Hypotheses
* `hom` – the model encloses the output equation
* `hh` – the output equation is affine
* `hx` – `x` lies in `R`
* `hy` – `y` lies in `R_y`
* `hu` – `u` lies in `U`

## Conclusion
* the output of the point lies in the float linear output set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet Plus Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.OutputFloatModel.outputSetLinearFloat_outer (sys : NonlinDASys n p m)
    (om : NonlinDASys.OutputFloatModel 𝕋 n p m sys.q)
    (hom : NonlinDASys.OutputFloatModel.Encloses sys om)
    (c : Vec ℝ sys.q) (M_x : Mat ℝ sys.q n) (M_y : Mat ℝ sys.q p) (M_u : Mat ℝ sys.q m)
    (hh : ∀ x y u, sys.h x y u = c + M_x *ᵥ x + M_y *ᵥ y + M_u *ᵥ u)
    (p_x : Vec 𝕋 n) (p_y : Vec 𝕋 p) (p_u : Vec 𝕋 m) (R : Zonotope (Vec 𝕋 n))
    (R_y : Zonotope (Vec 𝕋 p)) (U : Zonotope (Vec 𝕋 m))
    {x : Vec ℝ n} {y : Vec ℝ p} {u : Vec ℝ m} (hx : x ∈ R.construct) (hy : y ∈ R_y.construct)
    (hu : u ∈ U.construct) : -- --- CONCL ---
    sys.h x y u ∈ (om.outputSetLinearFloat p_x p_y p_u R R_y U).construct := by -- --- PROOF ---
  -- the real centers, their point boxes, and each shifted set holding its deviation
  set px := toRealVec p_x with hpx
  set py := toRealVec p_y with hpy
  set pu := toRealVec p_u with hpu
  have hsh : ∀ {k : ℕ} {Z : Zonotope (Vec 𝕋 k)} {z : Vec ℝ k} (v : Vec 𝕋 k), z ∈ Z.construct →
      z - toRealVec v ∈ (Z ⊞ Zonotope.point (-v)).construct := fun v hz => by
    have h := Plus.plus_outer (S := Zonotope (Vec 𝕋 _)) _ _ (Set.add_mem_add hz
      (show toRealVec (-v) ∈ (Zonotope.point (-v)).construct by
        rw [Zonotope.construct_point]; exact rfl))
    rwa [toRealVec_neg, ← sub_eq_add_neg] at h
  have hPx := Interval.mem_point p_x
  have hPy := Interval.mem_point p_y
  have hPu := Interval.mem_point p_u
  -- the Jacobians of the affine output at the centers are its matrices
  have hJx : jacobianMat (fun x => sys.h x py pu) px = M_x := by
    have := jacobianMat_affine (c + M_y *ᵥ py + M_u *ᵥ pu) M_x px
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  have hJy : jacobianMat (fun y => sys.h px y pu) py = M_y := by
    have := jacobianMat_affine (c + M_x *ᵥ px + M_u *ᵥ pu) M_y py
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  have hJu : jacobianMat (fun u => sys.h px py u) pu = M_u := by
    have := jacobianMat_affine (c + M_x *ᵥ px + M_y *ᵥ py) M_u pu
    simpa [hh, add_assoc, add_comm, add_left_comm] using this
  -- the value at the centers, and the three blocks applied to their deviations
  have h0 := Interval.zonotope_contains _ (hom.h_mem _ _ _ _ hPx _ hPy _ hPu)
  have hX := Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (om.jacX (Interval.point p_x) (Interval.point p_y) (Interval.point p_u))
    (R ⊞ Zonotope.point (-p_x)) (Set.mem_biUnion
      (hJx ▸ hom.jacX_mem _ _ _ _ hPx _ hPy _ hPu) (Set.mem_image_of_mem _ (hsh p_x hx)))
  have hY := Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (om.jacY (Interval.point p_x) (Interval.point p_y) (Interval.point p_u))
    (R_y ⊞ Zonotope.point (-p_y)) (Set.mem_biUnion
      (hJy ▸ hom.jacY_mem _ _ _ _ hPx _ hPy _ hPu) (Set.mem_image_of_mem _ (hsh p_y hy)))
  have hU := Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
    (om.jacU (Interval.point p_x) (Interval.point p_y) (Interval.point p_u))
    (U ⊞ Zonotope.point (-p_u)) (Set.mem_biUnion
      (hJu ▸ hom.jacU_mem _ _ _ _ hPx _ hPy _ hPu) (Set.mem_image_of_mem _ (hsh p_u hu)))
  -- the output is the value at the centers plus the three first-order terms
  have hid : sys.h x y u = sys.h px py pu
      + M_x *ᵥ (x - px) + M_y *ᵥ (y - py) + M_u *ᵥ (u - pu) := by
    simp only [hh, Matrix.mulVec_sub]
    abel
  rw [hid]
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 sys.q)) _ _ (Set.add_mem_add
    (Plus.plus_outer (S := Zonotope (Vec 𝕋 sys.q)) _ _ (Set.add_mem_add
      (Plus.plus_outer (S := Zonotope (Vec 𝕋 sys.q)) _ _ (Set.add_mem_add h0 hX)) hY)) hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
