module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerDecTwTOfStd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPairStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuplesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem twistedPeriodAdmissible_of_rowInt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (nch : NChoice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (tp : Formalism.L2.Host.TupTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.cf l Z) nch), tp.xi = I.xi → ∀ Y : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G), Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) Y (I.tw l l0 Z) := by
  intro B X I hOk hPins l Z l0 hRow nch tp hxi Y
  obtain ⟨C, hC, hLv⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns I hOk hPins l Z
  obtain ⟨t, ht⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData I hOk hPins l Z l0 nch tp C hxi hC hLv
  have hT := GlobalTheory.PerTwClose.perDecTwT_of_std I hOk l Z l0 hRow (I.cf l Z) nch tp C t Y ht
  refine GlobalTheory.T.admissiblePeriodTwists_reduction_placeTuples (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) Y (I.tw l l0 Z) ?_
  intro u μ hμ _
  exact GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.cf l Z) nch tp C (I.tw l l0 Z) t Y u μ hμ (hT u μ hμ)

end GlobalTheory.PerTwClose
