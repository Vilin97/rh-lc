module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rgExh_pack : CompanionTheory.RgExh.Dec.L.Pack := by
  first | exact @GlobalTheory.CompanionTheory.PackEmb.pack | exact GlobalTheory.CompanionTheory.PackEmb.pack | (intros; apply GlobalTheory.CompanionTheory.PackEmb.pack <;> assumption)
