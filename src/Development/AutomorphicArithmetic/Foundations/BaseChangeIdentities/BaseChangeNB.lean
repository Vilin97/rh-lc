module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FinalAllB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PJEigB

@[expose] public section

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F in
theorem UpperTheory.BaseChangeIdentities.baseChangeNB : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  Plug2B.bci_of (UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin UpperTheory.BaseChangeIdentities.uSide (FX.candFin_of_jEigFin Tail.JB.jEigFin))
    UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound FinalAllB.frameRead_holdsB
