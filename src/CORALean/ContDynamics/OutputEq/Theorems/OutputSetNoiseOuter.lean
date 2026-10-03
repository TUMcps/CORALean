import CORALean.ContDynamics.OutputEq.Operations.OutputSetNoise
import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

/-!
# `outputSetNoise` contains the output at every state, input and noise value

`outputSet_outer` for `C x + D u`, then the offset and the noise term are put back by `plus`
and `mtimes`. An enclosure, not an equality: each term is enclosed separately.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m q r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.outputSetNoise_outer (out : OutputEq 𝕋 n m r) (k : Vec 𝕋 r) (F : Mat 𝕋 r q)
    (R : S n) (U : S m) (V : S q) {x : Vec ℝ n} {u : Vec ℝ m} {v : Vec ℝ q}
    (hx : x ∈ construct R) (hu : u ∈ construct U) (hv : v ∈ construct V) :
    out.eval x u + toRealVec k + toRealMat F *ᵥ v ∈ construct (out.outputSetNoise k F R U V) :=
  plus_outer _ _ (Set.add_mem_add
    (plus_outer _ _ (Set.add_mem_add (out.outputSet_outer R U hx hu)
      (OfScalarPoint.mem_ofVec k)))
    (mtimes_outer F V (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hv))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
