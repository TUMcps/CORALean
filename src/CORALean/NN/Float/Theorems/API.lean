import CORALean.NN.Float.Theorems.CompressionPreprocessingOuter
import CORALean.NN.Float.Theorems.ReduceOnTheFlyOuter

/-!
# What the float network reduction guarantees, collected

The float counterparts of the exact layer's reduction theorems, stated as image inclusions
rather than through `ReducesAt`: that relation names the exact layers, and an instance of a
float network, its error boxes at real values, is a network no float layer can store.
`ReduceOnTheFlyOuter` is the on-the-fly reduction and `CompressionPreprocessingOuter` the
compression that runs it.
-/
