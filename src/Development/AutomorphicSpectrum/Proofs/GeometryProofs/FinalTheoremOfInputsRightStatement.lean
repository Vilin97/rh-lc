module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidanceStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspHeightUpper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSumStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLowerStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFarguesStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.NormNum.Parity
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHoldsStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidanceStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspHeightUpperStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.cusp_height_upper : Top.Given → Fl.FlatDegree → ∃ Ch : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied → HtU S' Ch (hostRd E) (hostLval H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given | exact GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := GlobalTheory.T.cusp_height_upper hG hF
  obtain ⟨Cu, hCu⟩ := GlobalTheory.T.cusp_volume_sum hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨GlobalTheory.T.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstantsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.exists_geometric_height_constants : Top.Given → Out.WeilSt → Fl.FlatDegree → ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | exact GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheoremStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.good_tower_volume_theorem : Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW GlobalTheory.T.FlatDegree_holds) (GlobalTheory.T.model_on_hodge_from_family hFam)
      (GlobalTheory.T.triv_flag_on_hodge_of_fargues hFHT) GlobalTheory.T.FlatDegree_holds GlobalTheory.T.TwistAut_holds hPair (GlobalTheory.T.comparison_of_inputs_avoidance hPB hAv hR)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpHodgeTiedHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.CmpHodgeTied_holds : GlobalTheory.CompanionTheory.Ar.HodgeComparisonCompatibility :=
  PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputsStatement

section

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cmpPair_of_inputs : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | exact GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsRight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_volume_of_reduced : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine hPts hAvoid hQ hZ hTheta
  have hGiven : Top.Given :=
    ⟨hM, hKF, hSA, hNS, hResK, GlobalTheory.T.semi_abelian_statement_holds, hFHT, hGaga,
      (GlobalTheory.T.slope_bound_of_line_large_degree hLLD).1, hPB, hHS, hAn, hNine,
      GlobalTheory.T.antisymmetric_perturbation_holds⟩
  have hW : Out.WeilSt := GlobalTheory.CompanionTheory.Ar.Link.weilSt
  have hHTD : GR.HodgeTateDatumStatement := GlobalTheory.CompanionTheory.Ar.GR.Top.main
  have hOrd : GR.OrdinaryCurveStatement := GlobalTheory.T.ordinary_curve_statement_holds
  have hFam : Num.FamilyExistsPos := GlobalTheory.T.family_pos_of_hodge_tate_inputs hFHT hQ hZ hHTD hOrd
  have hCmpSt : Cmp.CmpSt := GlobalTheory.T.comparison_of_inputs_avoidance hPB hAvoid hResK
  have hTied : HodgeComparisonCompatibility := GlobalTheory.T.CmpHodgeTied_holds
  have hPair : Cmp.CmpPair := GlobalTheory.T.cmpPair_of_inputs hPB hCmpSt hTied hTheta
  exact GlobalTheory.T.good_tower_volume_theorem hGiven hPts hAvoid hW hFam hPair

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsRightStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.final_theorem_of_inputs_right : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.goodTower_volume_of_reduced | exact GlobalTheory.CompanionTheory.Ar.Top.goodTower_volume_of_reduced | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.goodTower_volume_of_reduced <;> assumption)
end
end
