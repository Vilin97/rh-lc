module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

@[expose] public section

namespace CompanionTheory.Lime.BM

theorem inputs : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs := by
  refine ⟨Formalism.L2.SG.OwnFacts.factDecLow.out, Formalism.L2.SG.BesselDiscreteSeries.decInf, ?_, trivial⟩
  first
    | exact Formalism.L2.SG.Pf.k_finite_smooth
    | exact Formalism.L2.SG.Pf.k_finite_smooth_bessel

end CompanionTheory.Lime.BM
