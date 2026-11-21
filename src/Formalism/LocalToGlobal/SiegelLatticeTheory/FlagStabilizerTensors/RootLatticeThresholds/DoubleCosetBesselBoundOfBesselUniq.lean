module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeCS3dClosed

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄


theorem inputs_of (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs :=
  ⟨Formalism.L2.SG.BesselDiscreteSeries.decLow, hDI, Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth, hJ⟩

end Formalism.MainNotions.BridgeCS3dClosed
