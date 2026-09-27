import CORALean.Examples.Bench.Rational

/-!
# The unsound baseline: bound propagation in round-to-nearest binary32

What a typical verifier that trusts its floats does, written out so the baseline
`nn-float32` compares against is reproducible rather than described: interval
bound propagation (IBP) and DeepZ-style zonotope propagation through an affine,
ReLU, affine network, every operation Lean's native `Float32` in round-to-nearest,
with no rounding error accounted for anywhere. Nothing here is proved, and nothing
here should be: it is the thing the sound analysis is measured against, and
`experiments/nn/naive_float32.py` recomputes every number it prints.

`pointEval` is the network itself at one input, generic in the arithmetic, so the
same code runs it exactly (`ExactDyadic`) and as deployed (`Float32`). Every dot
product sums left to right from zero and adds the bias last, in all three, so
the only difference between them is the rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

/-- `d` in binary32. Exact whenever `d` fits 24 significand bits, which the caller
checks: through the double first, exact below 53 bits, then rounded once. -/
def ExactDyadic.toFloat32 (d : ExactDyadic) : Float32 := d.toFloatUnchecked.toFloat32

namespace Nn

/-- One affine layer, `W` stored by rows: `x ↦ W x + b`. -/
structure Layer (α : Type) where
  W : Array (Array α)
  b : Array α

def Layer.map {α β : Type} (f : α → β) (L : Layer α) : Layer β :=
  ⟨L.W.map (·.map f), L.b.map f⟩

/-- The four operations a point evaluation needs, passed explicitly so the one
`pointEval` below serves exact dyadics and binary32 alike. -/
structure Arith (α : Type) where
  zero : α
  add : α → α → α
  mul : α → α → α
  relu : α → α

/-- `Σⱼ wⱼ xⱼ`, from zero and left to right: the order every analysis here uses. -/
def dot {α : Type} (A : Arith α) (w x : Array α) : α :=
  (Array.zipWith A.mul w x).foldl A.add A.zero

def affine {α : Type} (A : Arith α) (L : Layer α) (x : Array α) : Array α :=
  Array.zipWith (fun row bi => A.add (dot A row x) bi) L.W L.b

/-- `W₂ relu(W₁ x + b₁) + b₂`: the network at one input. -/
def pointEval {α : Type} (A : Arith α) (L₁ L₂ : Layer α) (x : Array α) : Array α :=
  affine A L₂ ((affine A L₁ x).map A.relu)

/-- Exact: every weight and input is dyadic, so the network's value is one too. -/
def exactArith : Arith ExactDyadic :=
  ⟨ExactDyadic.zero, ExactDyadic.add, ExactDyadic.mul,
    fun x => if x.mantissa < 0 then ExactDyadic.zero else x⟩

/-- Round-to-nearest binary32, the hardware's own operations. -/
def f32Arith : Arith Float32 := ⟨0, (· + ·), (· * ·), fun x => if x < 0 then 0 else x⟩


/-! ## Naive interval bound propagation -/

/-- A box, `lo ≤ x ≤ hi` coordinatewise. -/
structure Box32 where
  lo : Array Float32
  hi : Array Float32

/-- Per row, the lower bound takes `lo` where the weight is nonnegative and `hi`
where it is negative, the upper bound the other way round; bias added last. -/
def ibpAffine (L : Layer Float32) (X : Box32) : Box32 :=
  let row (w : Array Float32) (bi : Float32) : Float32 × Float32 :=
    let (l, u) := (Array.zip w (Array.zip X.lo X.hi)).foldl (fun (l, u) (wj, lj, uj) =>
      if 0 ≤ wj then (l + wj * lj, u + wj * uj) else (l + wj * uj, u + wj * lj)) (0, 0)
    (l + bi, u + bi)
  let rows := Array.zipWith row L.W L.b
  ⟨rows.map (·.1), rows.map (·.2)⟩

def ibpRelu (X : Box32) : Box32 := ⟨X.lo.map f32Arith.relu, X.hi.map f32Arith.relu⟩


/-! ## Naive zonotope propagation (DeepZ) -/

/-- `{c + Σₖ βₖ gₖ | βₖ ∈ [-1, 1]}`, each generator `gₖ` a vector as long as `c`. -/
structure Zono32 where
  c : Array Float32
  G : Array (Array Float32)

/-- `W c + b` for the center, `W gₖ` for each generator. -/
def zonoAffine (L : Layer Float32) (Z : Zono32) : Zono32 :=
  ⟨affine f32Arith L Z.c, Z.G.map fun g => L.W.map fun row => dot f32Arith row g⟩

/-- `Σₖ |gₖ i|` per coordinate: the zonotope's radius, in the same arithmetic. -/
def zonoRadius (Z : Zono32) : Array Float32 :=
  Z.G.foldl (fun r g => Array.zipWith (fun ri gi => ri + gi.abs) r g) (Z.c.map fun _ => 0)

/-- DeepZ's ReLU per neuron: identity when `l ≥ 0`, zero when `u ≤ 0`, and
otherwise slope `λ = u / (u - l)` with offset `μ = -λ l / 2` and a new generator `μ`. -/
def zonoRelu (Z : Zono32) : Zono32 :=
  let r := zonoRadius Z
  let lam := Array.zipWith (fun c ri =>
    let l := c - ri
    let u := c + ri
    if 0 ≤ l then ((1 : Float32), (0 : Float32))
    else if u ≤ 0 then (0, 0)
    else let s := u / (u - l); (s, -(s * l) / 2)) Z.c r
  let c := Array.zipWith (fun c (s, mu) => s * c + mu) Z.c lam
  let G := Z.G.map fun g => Array.zipWith (fun gi (s, _) => s * gi) g lam
  -- one fresh generator per crossing neuron, `μ` in its own coordinate
  let fresh := (lam.mapIdx fun i (_, mu) => (i, mu)).filter (·.2 != 0) |>.map fun (i, mu) =>
    lam.mapIdx fun j _ => if j = i then mu else 0
  ⟨c, G ++ fresh⟩

/-- The interval hull `c ± Σₖ |gₖ|`, rounded to nearest like everything above. -/
def Zono32.box (Z : Zono32) : Box32 :=
  let r := zonoRadius Z
  ⟨Array.zipWith (· - ·) Z.c r, Array.zipWith (· + ·) Z.c r⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Affine, ReLU, affine, on boxes, in round-to-nearest binary32. -/
def ibp (L₁ L₂ : Layer Float32) (X : Box32) : Box32 :=
  ibpAffine L₂ (ibpRelu (ibpAffine L₁ X))

/-- Affine, ReLU, affine, on zonotopes, in round-to-nearest binary32. -/
def zono (L₁ L₂ : Layer Float32) (Z : Zono32) : Zono32 :=
  zonoAffine L₂ (zonoRelu (zonoAffine L₁ Z))

end Nn

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
