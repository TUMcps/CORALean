module

public import CORALean.ContSet.Conversion.Real.API
public import CORALean.ContSet.Conversion.Float.API

/-!
# Conversions between representations, both layers

One file per ordered pair — `<Source>_to_<Target>.lean` — so a new pair costs a
file rather than a directory, and no representation ever imports another. The file states what
the pair guarantees; what it builds is in the file of the same name in `Operations/`.
-/
