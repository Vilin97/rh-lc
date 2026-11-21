module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n2_top_real : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  first | exact @GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | exact GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T | (intros; apply GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T <;> assumption)
