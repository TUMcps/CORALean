module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.isFullDim`, over a floating-point scalar

CORA's `@ellipsoid/isFullDim` asks for `rank(Q) = n`, which rounding cannot decide. A sound test
instead checks a caller-proposed right inverse `H` of the generator matrix (a `k × n` float
matrix, a pseudo-inverse computed anywhere): if `G H` is strictly diagonally dominant, with the
products bracketed by directed roundings and the comparison certified by `ltStrict`, it is
invertible (Gershgorin), so `rank G = n`. The error box must be nonempty (`inf ≤ sup` by `le`),
so that the set is a translate-containing sum. Only `true` is certain.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isFullDim (E : Ellipsoid 𝕋 n) (H : Mat 𝕋 E.k n) : Bool :=
  -- `(G H)_{il}` between its two roundings: a lower bound on the diagonal, a magnitude elsewhere
  let diagLo : Fin n → 𝕋 := fun i => dotDown (fun j => E.G i j) (fun j => H j i)
  let mag : Fin n → Fin n → 𝕋 := fun i l =>
    maximum (dotUp (fun j => E.G i j) (fun j => H j l))
      (neg (dotDown (fun j => E.G i j) (fun j => H j l)))
  let offDiag : Fin n → 𝕋 := fun i => sumUp fun l => if l = i then zero else mag i l
  (List.finRange n).all fun i =>
    ltStrict (offDiag i) (diagLo i) && le (E.I_error.inf i) (E.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
