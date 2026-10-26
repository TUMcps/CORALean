module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate
public import CORALean.ContSet.Zonotope.Float.Operations.BallB
public import CORALean.ContSet.Zonotope.Float.Operations.BallCert

@[expose] public section

/-!
# `SpectraShadow.isFullDim`, over a floating-point scalar

A sufficient test for CORA's `@spectraShadow/isFullDim`, which decides the interior of a
semidefinite program's image. The caller names a coefficient vector `β` and a radius `δ`; the test
checks that the matrices are symmetric, that `A₀ + Σ γₗ Aₗ` is diagonally dominant, hence positive
semidefinite, for every `γ` within `δ` of `β` (each entry between two roundings, the spread `δ Σ
|Aₗ|` rounded up), that `δ` is positive, that the generators reach a ball (`ballCert` at the
Gram-matrix right inverse, so they span) and that the error box is ordered. Then the image of a
box of coefficients is open in the shadow. Only `true` is certain; CORA's `norm(G, 'fro') < 1e-8`
shortcut is not modelled.

## Inputs
* `S` – spectrahedral shadow
* `β` – center of the coefficient box
* `δ` – radius of the coefficient box

## Output
* `true` when the shadow is certified to have an interior point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.isFullDim (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (β : Vec 𝕋 S.m) (δ : 𝕋) : Bool :=
  -- what the coefficient box adds to each entry of `A₀ + Σ βₗ Aₗ`
  let spread : Fin S.k → Fin S.k → 𝕋 := fun i j => mulUp δ (sumUp fun l => absolute (S.A l i j))
  -- each entry of the combination over the box between its two roundings, and its magnitude
  let entryLo : Fin S.k → Fin S.k → 𝕋 := fun i j =>
    subDown (addDown (S.A₀ i j) (dotDown β fun l => S.A l i j)) (spread i j)
  let entryHi : Fin S.k → Fin S.k → 𝕋 := fun i j =>
    addUp (addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)) (spread i j)
  let mag : Fin S.k → Fin S.k → 𝕋 := fun i j => maximum (entryHi i j) (neg (entryLo i j))
  let offDiag : Fin S.k → 𝕋 := fun i => sumUp fun j => if j = i then zero else mag i j
  let symmetric : Bool := (List.finRange S.k).all fun i => (List.finRange S.k).all fun j =>
    le (S.A₀ i j) (S.A₀ j i) && (List.finRange S.m).all fun l => le (S.A l i j) (S.A l j i)
  let dominant : Bool := (List.finRange S.k).all fun i => le (offDiag i) (entryLo i i)
  -- the generators reach a ball around the origin, so the map `β ↦ G β` is onto
  let H := Zonotope.rightInvCandidate fun i j => S.G j i
  let reach := Zonotope.ballCert (fun i j => S.G j i) H (Zonotope.ballB H one) one
  symmetric && dominant && ltStrict zero δ && reach &&
    (List.finRange n).all fun i => le (S.I_error.inf i) (S.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
