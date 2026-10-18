module

public import CORALean.ContDynamics.Conform.Definitions.Conformant
public import CORALean.ContDynamics.Conform.Definitions.DevSet
public import CORALean.ContDynamics.Conform.Definitions.Glo
public import CORALean.ContDynamics.Conform.Definitions.IntervalNorm
public import CORALean.ContDynamics.Conform.Definitions.PassesBF
public import CORALean.ContDynamics.Conform.Definitions.ReachOutExact
public import CORALean.ContDynamics.Conform.Definitions.State
public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import CORALean.ContDynamics.Conform.Definitions.ZonoConformal

/-!
# What a reachset-conformance statement is about

The model's runs (`State`) and reachable sets (`ReachOutExact`), the deviation set the
nominal run is subtracted into (`DevSet`), test cases and conformance tested on them
(`Conformant`), the stretched templates the identified sets are (`TemplateZono`), the
sizes a synthesis minimizes (`IntervalNorm`), and the general linear output
approximation of an arbitrary model (`Glo`).
-/
