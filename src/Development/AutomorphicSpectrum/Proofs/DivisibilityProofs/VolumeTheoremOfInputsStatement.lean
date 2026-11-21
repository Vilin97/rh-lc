module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_theorem_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) → HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs <;> assumption)
