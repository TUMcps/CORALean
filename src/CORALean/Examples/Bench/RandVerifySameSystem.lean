import CORALean.Examples.Bench.RandVerifyInstance

/-!
# `randverify`: whether two instances state the same system

Equal `A`, `B`, `C`, `X0`, `U` and `tend`, as exact rationals; the unsafe boxes may differ. Two
such instances have the same reachable set at every type and setting, so a run reaches it once.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def RandInstance.sameSystem (I J : RandInstance) : Bool :=
  I.A == J.A && I.B == J.B && I.C == J.C && I.x0 == J.x0 && I.u == J.u && I.tend == J.tend

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
