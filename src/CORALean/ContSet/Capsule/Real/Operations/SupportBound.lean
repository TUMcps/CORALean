import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.Global.EuclideanNorm
import CORALean.Global.LinProg.API

/-!
# A capsule answers a direction by its segment and its ball

`Capsule.construct` is a segment thickened by a Euclidean ball, so a linear
functional's value at any point splits the same way: the segment contributes
at most `|f g|`, moving `t` to whichever endpoint favours `f`, and the ball
contributes at most `r * ‖f‖₂` by Cauchy–Schwarz — `dotProduct_le_norm₂_mul_norm₂`
from `Global.EuclideanNorm`, the same lemma `Ellipsoid.supportBound` uses.

No `0 ≤ C.r` hypothesis: the membership witness already bounds the ball term's
norm by `C.r` itself, whatever its sign, so `C.r < 0` (denoting `∅`) needs no
separate case — unlike `construct_eq_add`, this proof never turns the bound
around into a squared one, which is the only step that needed `0 ≤ C.r`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No `0 ≤ C.r`: the membership witness already bounds the ball term by
`C.r`, whatever its sign, so `C.r < 0` (denoting `∅`) needs no separate case. -/
noncomputable def Capsule.supportBound (C : Capsule n) (f : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound C.construct f where
  val := f C.c + |f C.g| + C.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2)
  le := by
    intro x hx
    obtain ⟨t, ht, hle⟩ := hx
    -- `y` is the remainder off the segment point, `w` the functional's coefficients
    set y : Vec ℝ n := fun i => x i - (C.c i + t * C.g i) with hy_def
    set w : Vec ℝ n := fun i => f (Pi.single i 1) with hw_def
    have hyr : ‖y‖₂ ≤ C.r := hle
    -- `f`'s basis expansion turns `f y` into the dot product `y ⬝ᵥ w`
    have hfy : f y = y ⬝ᵥ w := by
      conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have heq : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i (1 : ℝ) := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [heq, smul_eq_mul]
    -- the ball: Cauchy–Schwarz bounds `f y` by `‖y‖₂ * ‖w‖₂`, then `‖y‖₂ ≤ C.r`
    have hball : f y ≤ C.r * ‖w‖₂ :=
      hfy ▸ (dotProduct_le_norm₂_mul_norm₂ y w).trans
        (mul_le_mul_of_nonneg_right hyr (norm₂_nonneg w))
    -- the segment: `t ∈ [-1, 1]` keeps `t * f C.g` under `|f C.g|`
    have hseg : t * f C.g ≤ |f C.g| :=
      calc t * f C.g ≤ |t * f C.g| := le_abs_self _
        _ = |t| * |f C.g| := abs_mul t (f C.g)
        _ ≤ 1 * |f C.g| :=
          mul_le_mul_of_nonneg_right (abs_le.mpr (Set.mem_Icc.mp ht)) (abs_nonneg _)
        _ = |f C.g| := one_mul _
    have hxeq : x = C.c + t • C.g + y := by
      funext i
      simp only [hy_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    -- recombine: `f x = f C.c + t * f C.g + f y`, each summand bounded above
    calc f x = f (C.c + t • C.g + y) := by rw [hxeq]
      _ = f C.c + t * f C.g + f y := by rw [map_add, map_add, map_smul, smul_eq_mul]
      _ ≤ f C.c + |f C.g| + C.r * ‖w‖₂ := by linarith
      _ = f C.c + |f C.g| + C.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
