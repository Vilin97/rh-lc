module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.BciOf
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.FrameRead
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree

@[expose] public section

theorem UpperTheory.BaseChangeIdentities.baseChangeN_of (hCF : PositivityTheory.Rg.BcB.F.FX.CandFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  PositivityTheory.Rg.BcB.Plug2.bci_of (UpperTheory.HeckeLevelFrameExistence.frameEx_of_fin UpperTheory.BaseChangeIdentities.uSide hCF) UpperTheory.BaseChangeIdentities.FrameWordIdentity.frameBound
    UpperTheory.BaseChangeIdentities.GelfandReading.frameRead
