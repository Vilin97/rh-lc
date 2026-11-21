module

public import Development.AutomorphicSpectrum.Definitions.JetCones.KTypePosCone
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional

@[expose] public section

namespace GlobalTheory.CompanionTheory.DS

open CompanionTheory.D.LK (hMultAlg hKModExists hOrthCyc)

theorem dsUnique : DSUnique :=
  fun n ε lam H H' _ _ _ _ σ σ' hlam hσ hσ' =>
    DSUniq.ds_unique hMultAlg hKModExists hOrthCyc n ε lam H' H σ' σ hlam hσ' hσ

end GlobalTheory.CompanionTheory.DS
