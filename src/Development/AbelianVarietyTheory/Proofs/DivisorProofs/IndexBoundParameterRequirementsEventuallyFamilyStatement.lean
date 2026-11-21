import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthAllRun
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceChart
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UnramifiedCompanionChartCharacters
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexBoundParameterRequirements_eventually_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  first | exact @GlobalTheory.OntoSizeRows.sizeRows_along | exact GlobalTheory.OntoSizeRows.sizeRows_along | (intros; apply GlobalTheory.OntoSizeRows.sizeRows_along <;> assumption)
