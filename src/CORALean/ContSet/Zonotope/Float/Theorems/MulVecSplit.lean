module

public import CORALean.ContSet.Interval.Float.Operations.CenterMat
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A matrix of an interval matrix acts through its center and the leftover

`A` in the box `M` is `mid(M)` plus `A - mid(M)`, so `A x` is `mid(M) x + (A - mid(M)) x`: the
split `mtimesIntervalMat` is built on, for a zonotope and a constrained zonotope alike.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `A` splits into its action through the center matrix and the leftover. -/
theorem Zonotope.mulVec_split (IM : Interval (Mat 𝕋 m n)) (A : Mat ℝ m n) (x : Vec ℝ n) :
    A *ᵥ x = toRealMat (Interval.centerMat IM) *ᵥ x
      + (fun i j => A i j - toReal (Interval.centerMat IM i j)) *ᵥ x := by -- --- PROOF ---
  rw [← Matrix.add_mulVec]
  congr 1
  funext i j
  show A i j = toReal (Interval.centerMat IM i j) + (A i j - toReal (Interval.centerMat IM i j))
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
