module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.EuclideanNorm
public import CORALean.Global.StepOf
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Location.calcBasisPcaFloat`

CORA's `@location/calcBasis.m` at `options.enclose{i} = 'pca'`: the left singular vectors of
`[-G, G]`, `G` the generators of the reach sets of the crossing, projected on a hyperplane guard
`{x | cᵀx = d}` (`|c| = 1`) by `(I - c cᵀ)`, at most the `500` longest kept (by squared length,
stable). They are the left singular vectors of `G`, by decreasing singular value, here from ten
cyclic one-sided Jacobi (Hestenes) sweeps on the generators in the scalar's own arithmetic, which
CORA.cpp reproduces bit for bit. The columns are orthonormal up to rounding only and nothing about
that is assumed (`Location.zonoGirardMemberFloat` adds the defect). The error boxes are ignored.

## Inputs
* `p` – steps of the square root where the format has none of its own
* `R` – reach sets that meet the guard
* `hyp` – the hyperplane guard's normal `nv`, none for another guard

## Output
* orthonormal basis, up to rounding, the columns by decreasing singular value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `a / b`, for a divisor of either sign (`divUp` is for a positive one). -/
@[step_of Location.calcBasisPcaFloat]
def Location.step_pcaDiv (a b : 𝕋) : 𝕋 :=
  if FloatOps.le FloatOps.zero b then divUp a b else divUp (neg a) (neg b)

/-- The dot product of two columns, summed from the first entry, every step rounded up. -/
@[step_of Location.calcBasisPcaFloat]
def Location.step_pcaDot (a b : Array 𝕋) : 𝕋 :=
  (a.zip b).foldl (fun acc xy => addUp acc (mulUp xy.1 xy.2)) FloatOps.zero

/-- One Hestenes rotation of the columns `p` and `q` of `W` (the generators in the coordinates `p`
and `q`), applied to `W` and to the accumulated `V`, so that the two columns become orthogonal.
None where they are orthogonal up to `2⁻⁵²` of the product of their lengths. -/
@[step_of Location.calcBasisPcaFloat]
def Location.step_pcaRotate (sq : 𝕋 → 𝕋) (p q : ℕ) (W V : Array (Array 𝕋)) :
    Array (Array 𝕋) × Array (Array 𝕋) :=
  let wp := W.getD p #[]
  let wq := W.getD q #[]
  let α := Location.step_pcaDot wp wp                               -- the squared lengths
  let β := Location.step_pcaDot wq wq
  let γ := Location.step_pcaDot wp wq                               -- and the inner product
  -- `γ² ≤ 2⁻¹⁰⁴ α β` counts as orthogonal: a rotation by noise mixes a degenerate pair
  if FloatOps.le (mulUp γ γ) (mulUp (half^[104] one) (mulUp α β)) then (W, V)
  else
    let ζ := Location.step_pcaDiv (subUp β α) (addUp γ γ)
    let t := Location.step_pcaDiv (if FloatOps.le FloatOps.zero ζ then one else neg one)
      (addUp (absolute ζ) (sq (addUp one (mulUp ζ ζ))))              -- `sgn ζ / (|ζ| + √(1+ζ²))`
    let c := Location.step_pcaDiv one (sq (addUp one (mulUp t t)))
    let s := mulUp t c
    -- the columns `p` and `q` mix
    let mix := fun (M : Array (Array 𝕋)) =>
      let mp := M.getD p #[]
      let mq := M.getD q #[]
      (M.set! p ((mp.zip mq).map fun xy => subUp (mulUp c xy.1) (mulUp s xy.2))).set! q
        ((mp.zip mq).map fun xy => addUp (mulUp s xy.1) (mulUp c xy.2))
    (mix W, mix V)

/-- The generators of the sets, projected on the hyperplane with unit normal `c`, and at most the
`500` longest by squared length. -/
@[step_of Location.calcBasisPcaFloat]
def Location.step_pcaGenerators (c : Option (Vec 𝕋 n)) (R : List (Zonotope (Vec 𝕋 n))) :
    List (Vec 𝕋 n) :=
  let all : List (Vec 𝕋 n) := R.flatMap fun Z => (List.finRange Z.h).map fun j => Z.G j
  let proj : List (Vec 𝕋 n) := match c with
    | none => all
    | some c => all.map fun g =>                                      -- `(I - c cᵀ) g`
      let d := dotUp c g
      fun i => subUp (g i) (mulUp (c i) d)
  let len := fun (g : Vec 𝕋 n) => dotUp g g
  let sorted := proj.mergeSort fun a b => FloatOps.le (len b) (len a)  -- longest first, stable
  if proj.length ≤ 500 then proj else sorted.take 500


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `'pca'` basis of the sets `R` meeting the guard. -/
def Location.calcBasisPcaFloat (p : ℕ) (R : List (Zonotope (Vec 𝕋 n))) (hyp : Option (Vec 𝕋 n)) :
    Mat 𝕋 n n :=
  let sq := sqrtUp p
  -- the unit normal of a hyperplane guard
  let c := hyp.map fun nv =>
    let l := sq (dotUp nv nv)
    fun i => Location.step_pcaDiv (nv i) l
  let G := Location.step_pcaGenerators c R
  -- the generators by coordinate: column `i` holds the `i`-th entries
  let W : Array (Array 𝕋) := Array.ofFn fun i : Fin n => (G.map fun g => g i).toArray
  let I : Array (Array 𝕋) := Array.ofFn fun i : Fin n => Array.ofFn fun r : Fin n =>
    if i = r then one else FloatOps.zero
  -- ten cyclic sweeps over the pairs `p < q`
  let pairs := (List.range n).flatMap fun a => ((List.range n).filter (a < ·)).map (a, ·)
  let (W', V) := (List.range 10).foldl (fun st _ =>
    pairs.foldl (fun st pq => Location.step_pcaRotate sq pq.1 pq.2 st.1 st.2) st) (W, I)
  -- the singular vectors by decreasing length
  let len := fun i : ℕ => Location.step_pcaDot (W'.getD i #[]) (W'.getD i #[])
  let order := (List.range n).mergeSort fun i j => FloatOps.le (len j) (len i)
  fun r k => (V.getD (order.getD k.val k.val) #[]).getD r.val FloatOps.zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
