import Mathlib.Data.Sign.Basic
import CORALean.ContSet.Interval.Real.Operations.EBox
import Mathlib.Data.EReal.Basic

/-!
# `Interval.dirac`

CORA's `@interval/dirac`: an enclosure of the `n`-th derivative of the Dirac delta over the
box, from the signs of its bounds. `signI = sign(I)` is the box of signs; `s = signI.inf +
signI.sup` is `0` when the box straddles `0` (or is `{0}`), `±1` when `0` is an endpoint, `±2`
when `0` is outside. `n = 0` puts `sup = Inf` where `|s| ≤ 1`, `n = 1` opens one side at `0`
as an endpoint and both sides where `s = 0`, any `n ≥ 2` opens both sides where `|s| ≤ 1`.
The bounds are infinite, so the result is an `Interval.EBox`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def Interval.dirac (n : ℕ) (I : Interval (Vec ℝ m)) : Interval.EBox m :=
  let signInf : Fin m → ℤ := fun i => ((SignType.sign (I.inf i) : SignType) : ℤ)
  let signSup : Fin m → ℤ := fun i => ((SignType.sign (I.sup i) : SignType) : ℤ)
  let s : Fin m → ℤ := fun i => signInf i + signSup i
  if n = 0 then
    let resInf : Fin m → EReal := fun _ => 0
    let resSup : Fin m → EReal := fun i => if |s i| ≤ 1 then ⊤ else 0
    (resInf, resSup)
  else if n = 1 then
    let resInf : Fin m → EReal := fun i => if s i = 0 ∨ s i = 1 then ⊥ else 0
    let resSup : Fin m → EReal := fun i => if s i = 0 ∨ s i = -1 then ⊤ else 0
    (resInf, resSup)
  else
    let resInf : Fin m → EReal := fun i => if |s i| ≤ 1 then ⊥ else 0
    let resSup : Fin m → EReal := fun i => if |s i| ≤ 1 then ⊤ else 0
    (resInf, resSup)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
