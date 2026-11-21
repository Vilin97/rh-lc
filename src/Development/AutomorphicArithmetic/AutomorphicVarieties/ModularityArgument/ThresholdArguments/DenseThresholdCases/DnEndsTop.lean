module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlEHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryThreeInputsOfLiterature

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
theorem ends0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_u_alt hH (_root_.UpperTheory.V.Z.J.linkedUnlE_holds_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH))
end UpperTheory.V.Z.Win.Dn
end
