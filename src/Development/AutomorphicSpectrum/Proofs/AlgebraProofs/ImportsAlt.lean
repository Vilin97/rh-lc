module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.JoinPullbackAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
