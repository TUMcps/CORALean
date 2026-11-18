module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifySpecSet
public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonoSupportUpFloat
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifySpecHoldsFloat`, a zonotope inside a safe set or apart from an unsafe one

A safe set holds where the support along every row is below its offset. CORA decides an unsafe
set by a linear program with a tolerance (`aux_intersectionCheckFast`); here a Farkas certificate
`λ ≥ 0`, `inf_Z (H'λ)' y > λ'b`, checked in floats, keeps the zonotope apart from `{y | H y ≤ b}`.
The candidates: each row alone, and for `q = 2` the normals of the generators as nonnegative
combinations of two rows (Cramer's rule). Without a certificate the set is undecided (`false`):
the step is refined, never taken as apart.

## Inputs
* `Z` – float zonotope with a box, the output set of a step
* `S` – float safe or unsafe set

## Output
* whether the set is shown to hold on `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The Farkas test for the multipliers `λ` on the rows: `λ ≥ 0` and `λ'b < inf_Z (H'λ)' y`, with
`H'λ` between its products rounded down and up. -/
@[step_of LinearSys.verifySpecHoldsFloat]
def LinearSys.step_verifyFarkasFloat (Z : LinearSys.VerifyZono 𝕋 q) (rows : List (Vec 𝕋 q × 𝕋))
    (lam : List 𝕋) : Bool :=
  let pairs := rows.zip lam
  let hi := fun i => pairs.foldl (fun acc ab => addUp acc (mulUp ab.2 (ab.1.1 i))) zero
  let lo := fun i => pairs.foldl (fun acc ab => addDown acc (mulDown ab.2 (ab.1.1 i))) zero
  let lb := pairs.foldl (fun acc ab => addUp acc (mulUp ab.2 ab.1.2)) zero  -- ≥ λ'b
  lam.length == rows.length && lam.all (fun l => le zero l) &&
    ltStrict lb (neg (LinearSys.verifyZonoSupportUpFloat Z (-hi)
      (fun i => subUp (hi i) (lo i))))

/-- The multipliers of rows `i` and `j` that give the planar direction `d`, by Cramer's rule, if
the determinant is not `0`. -/
@[step_of LinearSys.verifySpecHoldsFloat]
def LinearSys.step_verifyCramerFloat (rows : List (Vec 𝕋 q × 𝕋)) (d₀ d₁ : 𝕋) (i j : ℕ) :
    Option (List 𝕋) :=
  let x := fun (k : ℕ) (c : ℕ) =>                                      -- entry `c` of row `k`
    match rows[k]? with
    | some ab => if h : c < q then ab.1 ⟨c, h⟩ else zero
    | none => zero
  let det := subUp (mulUp (x i 0) (x j 1)) (mulUp (x i 1) (x j 0))
  if le det zero && le zero det then none else
  let li := divUp (subUp (mulUp d₀ (x j 1)) (mulUp d₁ (x j 0))) det
  let lj := divUp (subUp (mulUp (x i 0) d₁) (mulUp (x i 1) d₀)) det
  some ((List.range rows.length).map fun k => if k = i then li else if k = j then lj else zero)

/-- Whether some multipliers certify that `Z` misses the unsafe set of the rows. -/
@[step_of LinearSys.verifySpecHoldsFloat]
def LinearSys.step_verifyApartFloat (Z : LinearSys.VerifyZono 𝕋 q) (rows : List (Vec 𝕋 q × 𝕋)) :
    Bool :=
  let r := rows.length
  let unit := fun k => (List.range r).map fun l => if l = k then one else zero
  let facet := (List.range r).any fun k => LinearSys.step_verifyFarkasFloat Z rows (unit k)
  let pairs := (List.range r).flatMap fun i => (List.range r).filterMap fun j =>
    if i < j then some (i, j) else none
  let normal := q == 2 && Z.G.any fun g =>                              -- the edge normals
    let g₀ := if h : 0 < q then g ⟨0, h⟩ else zero
    let g₁ := if h : 1 < q then g ⟨1, h⟩ else zero
    [(neg g₁, g₀), (g₁, neg g₀)].any fun d => pairs.any fun ij =>
      match LinearSys.step_verifyCramerFloat rows d.1 d.2 ij.1 ij.2 with
      | some lam => LinearSys.step_verifyFarkasFloat Z rows lam
      | none => false
  facet || normal


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A safe set: every row's support below its offset; an unsafe set: a Farkas certificate. -/
def LinearSys.verifySpecHoldsFloat (Z : LinearSys.VerifyZono 𝕋 q)
    (S : LinearSys.VerifySpecSet 𝕋 q) : Bool :=
  if S.safe then S.rows.all fun ab =>
    ltStrict (LinearSys.verifyZonoSupportUpFloat Z ab.1 fun _ => zero) ab.2
  else LinearSys.step_verifyApartFloat Z S.rows

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
