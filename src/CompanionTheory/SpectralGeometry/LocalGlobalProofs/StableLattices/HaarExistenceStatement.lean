module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HaarExistence : CompanionTheory.RgExh.Dec.L.HaarExists := by
  first | exact @GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | exact GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | (intros; apply GlobalTheory.CompanionTheory.ParabolicHaar.haarExists <;> assumption)
