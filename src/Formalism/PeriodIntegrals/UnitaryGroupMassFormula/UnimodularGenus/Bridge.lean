module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomLoc

@[expose] public section

namespace PI.UG.W

open NumberField

theorem isomLocStd : IsomLocStd := by
  intro E _ _ _ n hE N hN p hp hu
  exact ReciprocityTheory.ChartRestriction.L3.exists_isom_loc hE (hStd_isSymm E n) (stdLat_isOrtho E n) hN p hp hu

end PI.UG.W
