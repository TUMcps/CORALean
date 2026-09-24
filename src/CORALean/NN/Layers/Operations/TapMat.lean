import CORALean.NN.Layers.Operations.TapEntry

/-!
# The matrix of a stencil

Output `j` reads inputs `tap j l` with weight `w j l`, one row at a time through `tapEntry`, so
every entry is a stored weight or zero and nothing rounds. Convolution, average pooling and the
selection matrix max pooling encloses through are all this matrix at their own taps and weights.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Output `j` reads inputs `tap j l` with weight `w j l`. -/
def tapMat (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋) : Mat 𝕋 m n :=
  fun j i => tapEntry (tap j) (w j) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
