module

public import CORALean.ContSet.Interval.Float.Operations.Symmetric
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat

@[expose] public section

/-!
# How far `mtimesIntervalMat` reaches beyond one matrix of the box

`mtimesIntervalMat_outer` puts every `A *ᵥ Z` inside `[M] Z`; this box bounds
the other side, `[M] Z ⊆ A Z ⊕ box` for every `A` in `[M]`. It is what an inner
approximation through an interval matrix holding the true `e^{AΔt}` pays.

Three parts. `mid(M) Z`'s own rounding is `mtimesBox`. The perturbation
`(mid(M) - A) x`, for `x` anywhere in `Z`, is at most `|M - mid(M)| (|c| + Σ|G|
+ |E|)` per coordinate, and the diagonal generators `[M] Z` added for the
residual on the nominal part reach `|M - mid(M)| (|c| + Σ|G|)`; both go into one
symmetric box. The result's own error box is kept whole.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimesIntervalMat IM Z` holds beyond `A Z`, for any `A` in `IM`: `mid(M) Z`'s
rounding, `|M - mid(M)|` over all of `Z` and over the diagonal generators, and the error box. -/
def Zonotope.mtimesIntervalMatBox (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) :=
  let C := Interval.centreMat IM                                    -- mid(M), stored
  let Rs := Interval.matResidual IM.inf IM.sup C                    -- M - mid(M), a box
  let r : Mat 𝕋 m n := fun i j =>                                   -- |M - mid(M)|
    maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))
  let ν : Vec 𝕋 n := fun j =>                                       -- |c| + Σ|G|
    addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j)
  let ξ : Vec 𝕋 n := fun j =>                                       -- |c| + Σ|G| + |E|
    addUp (ν j) (maximum (absolute (Z.E.inf j)) (absolute (Z.E.sup j)))
  let b : Vec 𝕋 m := fun i => sumUp fun j => mulUp (r i j) (ν j)   -- diag(b)'s reach
  let a : Vec 𝕋 m := fun i => sumUp fun j => mulUp (r i j) (ξ j)   -- (mid(M) - A) x's reach
  (Zonotope.mtimesBox C Z).plus                                     -- mid(M) Z's rounding
    ((Interval.symmetric fun i => addUp (a i) (b i)).plus           -- a + b, symmetric
      (Zonotope.mtimesIntervalMat IM Z).E)                          -- [M] Z's own box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
