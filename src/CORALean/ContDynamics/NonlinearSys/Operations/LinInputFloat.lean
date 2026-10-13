import CORALean.ContDynamics.NonlinearSys.Operations.SlopeRemainder
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The input set a float linearization widens to

`linInput` in `𝕋`, in CORA's deviation coordinates `δ = x - x✱`:
`δ̇ = A δ + ũ(t)` with every admissible `ũ(t)` in `{f(x✱,u✱)} ⊕ B(U ⊖ u✱) ⊕ L`, as a
float zonotope. `linInput`'s `- A x✱` is gone with the shift, which is what keeps
the constant input small: it is the field at the expansion point, not that minus
a matrix times a state of any size. `f(x✱,u✱)` enters as the model's box at the
point; `U ⊖ u✱` is `recentre U`, the input set with its stored centre taken out,
so `u✱` is that centre and nothing is rounded there; `L` is `slopeRemainder`.

`X` and `U'` are boxes the caller certifies: `X` has to hold every state of the
step and `x✱`, `U'` every input and `u✱`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[f(x✱, u✱)] ⊕ B(U - u✱) ⊕ L` at `u✱ = U.c`, with `L` over the boxes `X`
and `U'`. -/
def NonlinearSys.FloatModel.linInputFloat (fm : NonlinearSys.FloatModel 𝕋 n m) (A : Mat 𝕋 n n)
    (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (X : Interval (Vec 𝕋 n)) (U : Zonotope (Vec 𝕋 m))
    (U' : Interval (Vec 𝕋 m)) : Zonotope (Vec 𝕋 n) :=
  let us := U.c                                                     -- u✱
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- [f(x✱, u✱)]
  let L := fm.slopeRemainder A B xs us X U'                         -- L, the abstraction error
  (f₀.zonotope ⊞ Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B
    (Recentre.recentre U)) ⊞ L.zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
