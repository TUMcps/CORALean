module

public import CORALean.ContSet.Interval.Float.Operations.EvalList
public import CORALean.Global.RecList
public import CORALean.Global.Float.InvSqrtOneSub
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# The `(j+1)`-th Taylor coefficient of `arcsin`, enclosed

`arcsin⁽ʲ⁺¹⁾ c = asinPoly j c · v²ʲ⁺¹` with `v = (√(1 - c²))⁻¹`, so the coefficient is
`asinPoly j c · v²ʲ⁺¹ / (j+1)!`: the integer polynomial (`recL [1, 0, -1] (j ↦ 2j+1) j`) by
`Interval.evalList` on `[c, c]`, `v²ʲ⁺¹` between `powDown` and `powUp` of the roundings of `v`
(`Global/Float/InvSqrtOneSub`), and `1 / (j+1)!` by `divFact`, the three through the corner
products. `q` is the precision of the square root.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.arcsinCoef (q : ℕ) (c : 𝕋) (j : ℕ) : Interval 𝕋 :=
  let P := Interval.evalList c c (recL [1, 0, -1] (fun j => 2 * (j : ℤ) + 1) j)
  let G := divFact ⟨one, one⟩ (j + 1)
  let W : Interval 𝕋 :=
    ⟨Interval.mulLo (powDown (invSqrtOneSubLo q c) (2 * j + 1))
        (powUp (invSqrtOneSubHi q c) (2 * j + 1)) G.inf G.sup,
      Interval.mulHi (powDown (invSqrtOneSubLo q c) (2 * j + 1))
        (powUp (invSqrtOneSubHi q c) (2 * j + 1)) G.inf G.sup⟩
  ⟨Interval.mulLo P.inf P.sup W.inf W.sup, Interval.mulHi P.inf P.sup W.inf W.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
