import CORALean.NN.Graph.Uncertain

/-!
# `Ã = A(λ) + I`, over the padded factor set

`uncertainAdj` with the self-loop added and `N` further factors appended, one
per node, that this set does not use at all: its generators over them are zero.

The padding is what lets the message-passing enclosure pair this set with the
two inverse-square-root sets. `PolyZonotope.bilin` asks its two arguments for
the *same* factors, and the inverse square roots need a factor each for the
residual their relaxation leaves — so every set in the product is written over
`m + N` factors, `m` edges and `N` residuals, and each of them ignores the ones
that are not its own. `Fin.addCases` is how a generator family splits along
that seam.

`E = identE (m + N)` still, so every generator is scaled by its own factor and
nothing else, and the point at a factor vector stays affine.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ã = A(λ) + I` as a matrix polynomial zonotope over `m + N` factors, the
last `N` of which it leaves to the inverse square roots. -/
noncomputable def GNN.uncertainAdjPad (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) :
    PolyZonotope (Mat ℝ N N) where
  p := m + N
  h := m + N
  q := 0
  c := A + 1 + ∑ e, (1/2 : ℝ) • GNN.edgeMat (U e)
  G := Fin.addCases (fun e => (1/2 : ℝ) • GNN.edgeMat (U e)) (fun _ => 0)
  E := PolyZonotope.identE (m + N)
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
