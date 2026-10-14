module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Float.Operations.IndepFactors
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral
public import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGenAll

@[expose] public section

/-!
# `PolyZonotope.containsSetApprox`

The set branch of CORA's `@polyZonotope/contains_` with `'approx'`, `aux_proveContainment`:
the inner set `S` is split along its longest generator
(`aux_splitLongestGen_`, `splitLongestGenAll`) for `splits = 8` rounds, one more while the list
does not grow, and a piece
is dropped once `aux_containsInterval` ([1, Alg. 3], `innerGeneral`) proves its interval
enclosure inside the image of `[-1, 1]ᵖ⁺ᵍ` under `aux_funcPoly` (`indepFactors`); `true` when
no piece is left (the rounds CORA still runs on the empty list change nothing, and are not run
here). CORA starts each test from `x + pinv(J(x))·(Y - center(Y))`, `x` from
`fmincon`; here that box is the caller's `guess`. `fuel` caps the rounds.

CORA first tries to disprove containment by a contractor (`aux_disproveContainment`), which only
ever returns `false`, and then returns `false` for an `S` that `isFullDim` does not certify;
the first is not formalized, the second is kept. `S` is a polynomial zonotope; CORA converts
other sets first. `true` is only returned where the error box holds `0`.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` proves `S ⊆ pZ`. -/
def PolyZonotope.containsSetApprox (pZ S : PolyZonotope (Vec 𝕋 n))
    (guess : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 (pZ.p + pZ.q)))
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter fuel : ℕ) : Bool :=
  -- fHan = aux_funcPoly(x, c, G, GI, E); X = interval(-onesVec, onesVec)
  let pZd : PolyZonotope (Vec 𝕋 n) := pZ.indepFactors
  let X : Interval (Vec 𝕋 (pZ.p + pZ.q)) := ⟨fun _ => neg one, fun _ => one⟩
  -- Y = interval(list{j}); isContained = aux_containsInterval(fHan, jacHan, X, X_, Y)
  let proven : PolyZonotope (Vec 𝕋 n) → Bool := fun T =>
    PolyZonotope.innerGeneral pZd X (guess T.interval) T.interval inv iter
  -- one round: list_, cnt, splits, and the answer once the rounds are over
  let step : List (PolyZonotope (Vec 𝕋 n)) × ℕ × ℕ × Option Bool →
      List (PolyZonotope (Vec 𝕋 n)) × ℕ × ℕ × Option Bool := fun s =>
    match s with
    | (L, cnt, splits, none) =>
      -- sets = aux_splitLongestGen_(list{j}) for the pieces not proved
      let L' := L.flatMap fun T => if proven T then [] else T.splitLongestGenAll
      -- splits = splits + 1 if cnt == splits and the list did not grow
      let splits' := if cnt = splits ∧ L' ≠ [] ∧ L'.length ≤ L.length then splits + 1 else splits
      -- while cnt <= splits; an empty list stays empty, so the loop stops there
      if cnt + 1 ≤ splits' ∧ L' ≠ [] then (L', cnt + 1, splits', none)
      else (L', cnt + 1, splits', some L'.isEmpty)
    | s => s
  -- the error box holds `0`, and S is full-dimensional
  ((List.finRange n).all fun i => le (pZ.I_error.inf i) zero && le zero (pZ.I_error.sup i)) &&
    S.isFullDim && ((step^[fuel] ([S], 1, 8, none)).2.2.2 == some true)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
