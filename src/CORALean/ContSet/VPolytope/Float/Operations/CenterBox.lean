module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.centerBox` over a floating-point scalar

CORA's `center` with method `'avg'`, `c = mean(V, 2)`, on the stored floats. The mean is a
quotient by the vertex count, which a float cannot hold exactly, so this returns a box around
it: per coordinate the vertex sum rounded down and up, divided by the count rounded up and by it
rounded down (at least `1`), the outer of the two quotients taken each way, which is sound for
either sign of the sum. The box is not a point of the set; `centerBox_meets` says it holds one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.centerBox (P : VPolytope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let kU : 𝕋 := nsmulUp P.k one                        -- the count, rounded up
  let kD : 𝕋 := maximum one (nsmulDown P.k one)        -- the count, rounded down, at least 1
  ⟨fun i => let s := sumDown fun l => P.V l i
     minimum (divDown s kU) (divDown s kD),
   fun i => let s := sumUp fun l => P.V l i
     maximum (divUp s kU) (divUp s kD)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
