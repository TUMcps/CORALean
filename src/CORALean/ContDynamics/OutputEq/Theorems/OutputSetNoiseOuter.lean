module

public import CORALean.ContDynamics.OutputEq.Operations.OutputSetNoise
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

@[expose] public section

/-!
# `outputSetNoise` contains the output at every state, input and noise value

`outputSet_outer` for `C x + D u + k`, then the noise term is put back by `mtimes` and
`plus`. An enclosure, not an equality: each term is enclosed separately.

## Inputs
* `out` – output equation
* `F` – noise matrix
* `R` – state set
* `U` – input set
* `V` – noise set
* `x` – state
* `u` – admissible input
* `v` – noise value

## Hypotheses
* `hx` – state in state set
* `hu` – input in input set
* `hv` – noise in noise set

## Conclusion
* the noisy output lies in the output enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m q r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OutputEq.outputSetNoise_outer (out : OutputEq 𝕋 n m r) (F : Mat 𝕋 r q)
    (R : S n) (U : S m) (V : S q) {x : Vec ℝ n} {u : Vec ℝ m} {v : Vec ℝ q}
    (hx : x ∈ construct R) (hu : u ∈ construct U) (hv : v ∈ construct V) :
    out.eval x u + toRealMat F *ᵥ v ∈ construct (out.outputSetNoise F R U V) :=
  plus_outer _ _ (Set.add_mem_add (out.outputSet_outer R U hx hu)
    (mtimes_outer F V (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hv))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
