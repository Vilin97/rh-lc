module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfCommute
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GoodPathReplicate
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar

@[expose] public section

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish (GlobalTheory.CompanionTheory.RgStart.startMod : StartMod)
    (GlobalTheory.CompanionTheory.RgSteps.pathFin : PathFin)
    (GlobalTheory.CompanionTheory.RgPath.pathExists : PathExists)
    (GlobalTheory.CompanionTheory.RgPath.pathEndNat : PathEndNat)
    (GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct : SimpleDistinct)
    (GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps : ScalarCharacterOfL2Embedding)
    (GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps : UnitarizableOfL2Embedding)
    (GlobalTheory.CompanionTheory.RgIso.isoFacts : IsoFacts)
    (GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS : CharOfAlgDS)
    (GlobalTheory.CompanionTheory.LowestDataIso.algUniq : AlgUniq)
    (GlobalTheory.CompanionTheory.LowestData.dataUniq : DataUniq)
    (GlobalTheory.CompanionTheory.RenumDS.dsOfArr : DSOfArr)
    (GlobalTheory.CompanionTheory.DSData.dsOfData : DSOfData)
    (GlobalTheory.CompanionTheory.KModOfStep.kModOf : KModOf)
    (GlobalTheory.CompanionTheory.ArrCount.arrCount : ArrCount)

end CompanionTheory.RgExh.Fin
