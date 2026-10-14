module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The canonical-form system at a given float `A`

`LinearSys.canonical` at a float scalar, whose `0` and `1` are `FloatOps`'s own rather than
`Zero` and `One` instances: `(A, I, 0, I, 0, 0, 0, I)`, every entry exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, I, 0, I, 0, 0, 0, I)`, every dimension `n`, at float entries. -/
abbrev LinearSys.canonicalFloat (A : Mat 𝕋 n n) : LinearSys 𝕋 n :=
  let I : Mat 𝕋 n n := fun i j => if i = j then one else zero
  ⟨n, n, n, n, A, I, fun _ => zero, I, fun _ _ => zero, fun _ => zero, fun _ _ => zero, I⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
