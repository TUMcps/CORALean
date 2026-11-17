module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.energyWeightFloat`, a proposed energy weight of a second-order system

`A = [[0, I, 0], [-K, -C, F], [0, 0, 0]]` (`h` positions, `h` velocities, `z` constant inputs) is
recognised exactly: rows `0, …, h-1` hold a single `1`, at `h + i`, the last `z` rows are zero. A
diagonal mass `d`, `d_j = d_i K_ij / K_ji` from the first earlier `i` coupled both ways (else `1`),
symmetrizes `K`; the proposal is `P = blockdiag(sym(DK), D, β I)`, the energy `qᵀDKq + vᵀDv` and a
weight `β = 2 Σ (DF)² / ((2r)² min d)` of the inputs that keeps its rate near `r`. Nothing about
`P` is proved: `MatExp.energyGrowthFloat` checks it. Any other matrix, or a mass not positive,
gives `none`, whatever its distance to the form.

## Inputs
* `A` – float system matrix
* `r` – positive float rate

## Output
* the number of positions `h` and the proposed weight, if `A` has the form
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `x = 0`, compared exactly. -/
@[step_of MatExp.energyWeightFloat]
def MatExp.step_isZeroFloat (x : 𝕋) : Bool := le x zero && le zero x

/-- The masses `d_0, …, d_{j-1}` extended by `d_j`: `d_i K_ij / K_ji` for the first `i < j` with
both entries nonzero, else `1`. -/
@[step_of MatExp.energyWeightFloat]
def MatExp.step_energyMassFloat (K : ℕ → ℕ → 𝕋) (d : Array 𝕋) (j : ℕ) : Array 𝕋 :=
  match (List.range j).find? fun i =>
      !(MatExp.step_isZeroFloat (K i j) || MatExp.step_isZeroFloat (K j i)) with
  | some i => d.push (divUp (mulUp (d.getD i one) (K i j)) (K j i))
  | none => d.push one


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The form's exact check, the masses, `β`, and the block-diagonal proposal. -/
def MatExp.energyWeightFloat (A : Mat 𝕋 n n) (r : 𝕋) : Option (ℕ × Mat 𝕋 n n) :=
  let a : ℕ → ℕ → 𝕋 := fun i j => if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else zero
  let zeroRow := fun i => (List.range n).all fun j => MatExp.step_isZeroFloat (a i j)
  let z := ((List.range n).reverse.takeWhile zeroRow).length             -- the trailing zero rows
  let h := (n - z) / 2
  let unitRow := fun i => (List.range n).all fun j =>                    -- a single `1`, at `h + i`
    if j = h + i then le (a i j) one && le one (a i j) else MatExp.step_isZeroFloat (a i j)
  if !(decide (0 < h) && decide (2 * h + z = n) && (List.range h).all unitRow) then none else
  -- the masses from `K = -A_vq`
  let K : ℕ → ℕ → 𝕋 := fun i j => neg (a (h + i) j)
  let d := (List.range h).foldl (MatExp.step_energyMassFloat K) #[]
  let m := d.foldl minimum (d.getD 0 one)
  if !(d.all fun x => ltStrict zero x) then none else
  -- `β` from `DF`, `F = A_vz`; `1` if there is no coupling
  let S := (List.range h).foldl (fun S i => (List.range z).foldl (fun S k =>
    let x := mulUp (d.getD i one) (a (h + i) (2 * h + k)); addUp S (mulUp x x)) S) zero
  let q := addUp r r
  let β₀ := divUp (addUp S S) (mulUp (mulUp q q) m)
  let β := if le β₀ zero then one else β₀
  -- the weight
  some ⟨h, fun i j =>
    if i.val < h ∧ j.val < h then
      half (addUp (mulUp (d.getD i one) (K i j)) (mulUp (d.getD j one) (K j i)))
    else if i = j then (if i.val < 2 * h then d.getD (i.val - h) one else β)
    else zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
