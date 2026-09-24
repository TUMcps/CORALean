import CORALean.Global.Mathlib

/-!
# The weights of an identity layer

The identity as an `Enclose` kind, which a skip connection is written with. It has no weights
but `dim`, the proof that the two dimensions agree, which `rfl` discharges where a layer is
built; `: Type` keeps a structure of one proof out of `Prop`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure IdentityLayer (n m : ℕ) : Type where
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
