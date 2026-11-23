module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U), (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  first | exact @GlobalTheory.encard_fibre_eq_encard_ringHom | exact GlobalTheory.encard_fibre_eq_encard_ringHom | (intros; apply GlobalTheory.encard_fibre_eq_encard_ringHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRankStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  first | exact @GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | (intros; apply GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_affine_etale_coordinates_generic_point : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  first | exact @GlobalTheory.GenericCoords.exists_affine_etale_coords | exact GlobalTheory.GenericCoords.exists_affine_etale_coords | (intros; apply GlobalTheory.GenericCoords.exists_affine_etale_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCoverStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  first | exact @GlobalTheory.CoverDeg.etale_pullback_coords | exact GlobalTheory.CoverDeg.etale_pullback_coords | (intros; apply GlobalTheory.CoverDeg.etale_pullback_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  first | exact @GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | exact GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | (intros; apply GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints

section

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverDeg

theorem exists_open_covering_charts : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ σ : k →+* ℂ, (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hδ
  obtain ⟨U₁, hU₁, hx₁, ht⟩ := GlobalTheory.T.exists_affine_etale_coordinates_generic_point hp
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_nbhd_generic hp hq π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover p π D _ _ U₁ U₂ hU₁ hx₁ ht hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun σ => ⟨fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩⟩
  · rw [GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDeg
end
end
end
