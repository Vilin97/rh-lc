module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioFieldStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Height.NumberField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLine
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncChartsStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeDegreeBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComapStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.component_data_intersection_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BigBlock.main | exact GlobalTheory.CompanionTheory.Ar.BigBlock.main | (intros; apply GlobalTheory.CompanionTheory.Ar.BigBlock.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ), CoordTie ℤ ξ x → L.IsVB r ⊤ → ∃ W : ChartBundle ℤ x r E, L.IsChartOf x W.lat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | exact GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.exists_positive_hermitian_line : ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)), IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧ ∀ W : Ideal (MRing J), IsArithVar W 1 → 0 ≤ II K J W 1 ![A] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | exact GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystemStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.global_snc_chart_system : GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  exact GlobalTheory.CompanionTheory.Ar.GeoModel.exists_geo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSncStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.smooth_generic_fibre_of_snc : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y e bd → SmoothGenericFibreM y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBound

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_componentData_origin : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem), IsFullIntersectionSystem II → Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sw : Bool), (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω) (W : CMType H → Type) (_ : ∀ τ, AddCommGroup (W τ)) (_ : ∀ τ, Module Ω (W τ)) (Dc : GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData II (CMType H) K J Ω W) (Hd : GroundTheory.Heights₂.Heights.LowerBoundFree.HodgeData Dc) (Or : CptOrigin Y S₀ Dc Hd), genPt Or.𝔐.ξ₀ = genPt ξ₀ ∧ Dc.S = S₁ ∧ Dc.j = (if sw then D.q else D.p) ∧ Or.bg = (if sw then Sum.inr else Sum.inl) ∧ Or.𝔐.OmVB ∧ ∀ p ∈ S₀ ∪ S₁, HT.HTFree Or.𝔐 p := by
  intro hG hW E _ _ _ H D Xo l c Y II hII hgl hp hq Ω₀ _ ξ₀ hξ S₀ S₁ sw hS₀ hS₁ hd hdisc
  obtain ⟨bg, sm, j, r, hbg, hj, hsmc, hr, hside, hne, hbgj, rfl, hj1, hj2⟩ :
      ∃ (bg sm : CMType H → CMType H ⊕ CMType H) (j r : ℕ),
        bg = (if sw then Sum.inr else Sum.inl) ∧ j = (if sw then D.q else D.p) ∧
        (sm = Sum.inl ∨ sm = Sum.inr) ∧ (∀ τ, labelRk D (sm τ) = r) ∧
        ((bg = Sum.inl ∧ sm = Sum.inr ∧ j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ j = D.q)) ∧
        (∀ τ, bg τ ≠ sm τ) ∧ (∀ τ, labelRk D (bg τ) = j) ∧ r = D.p + D.q - j ∧ 1 ≤ j ∧
        j ≤ D.p + D.q - 1 := by
    cases sw
    · refine ⟨Sum.inl, Sum.inr, D.p, D.q, by simp, by simp, Or.inr rfl, fun _ => rfl,
        Or.inl ⟨rfl, rfl, rfl⟩, fun _ => by simp, fun _ => rfl, by omega, hp, by omega⟩
    · refine ⟨Sum.inr, Sum.inl, D.q, D.p, by simp, by simp, Or.inl rfl, fun _ => rfl,
        Or.inr ⟨rfl, rfl, rfl⟩, fun _ => by simp, fun _ => rfl, by omega, hq, by omega⟩
  have hchart := GlobalTheory.T.global_snc_chart_system hG hW E H D Xo l c Y hgl hp hq Ω₀ ξ₀ hξ S₀ S₁ sm (D.p + D.q - j) hsmc hr hS₀ hS₁ hd hdisc
  obtain ⟨K, _, J, _, Ω, _, _, y, 𝔐, deg, bd, vdeg, vnum, vden, s, aMu, e₀, hK, hgen, hcov, hom, hfree,
    htr, hsnc, hbd, hR, htors, hvb, hvert, hvert2, hli, hspan, hdeg⟩ :=
    hchart
  have hn : D.dim = Fintype.card (CMType H) * j * (D.p + D.q - j) := by
    have h2 := (GlobalTheory.T.cm_host_rank_bounds E H).2.2
    have hmul : j * (D.p + D.q - j) = D.p * D.q := by
      rcases hside with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · rw [Nat.add_sub_cancel_left]
      · rw [Nat.add_sub_cancel, Nat.mul_comm]
    rw [Datum.dim, ← h2, Nat.mul_div_cancel_left _ (by norm_num), _root_.mul_assoc, _root_.mul_assoc, hmul]
  rw [hn] at htr hsnc
  have htie : CoordTie ℤ 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) := 𝔐.tie
  haveI := hK
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ htie htr
  obtain ⟨hcl, htor, hconj⟩ := GlobalTheory.T.boundary_points_closed 𝔐.X Ω 𝔐.ξ K J y (abLocus 𝔐.t.G) bd htie hbd
  obtain ⟨nc, χ, hcov'⟩ := GlobalTheory.T.exists_torus_stable_snc_charts K J Ω y _ bd hsnc harith htor
  obtain ⟨A, hAa, hApos, hAconj, hAh⟩ := GlobalTheory.T.exists_positive_hermitian_line II K J (mCoordIdeal y) hII
  have hLvb : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p)
      (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype).IsVB (D.p + D.q) ⊤ := fun τ => by
    have e : labelRk D (bg τ) + labelRk D (sm τ) = D.p + D.q := by
      rw [hbgj, hr]; omega
    simpa only [e] using GlobalTheory.T.pair_lattice_sum_comap E H D l (Xo l) c Y S₀ Ω K J y 𝔐 (bg τ) (sm τ) (hne τ)
  have hWb := fun τ => GlobalTheory.T.exists_chart_bundle 𝔐.X Ω 𝔐.ξ _ _ (segreCoord y) _ (D.p + D.q) htie (hLvb τ)
  choose Wb hWb using hWb
  have hbd' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w →
      (w ∈ mcPts (mCoordIdeal y) ∩ mcPts bd ↔ ¬ 𝔐.Interior z) := fun z w h =>
    ⟨fun hw => (hbd z w h).1 hw.2,
      fun hz => ⟨(GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie w).2 ⟨z, 𝔐.all _, h⟩, (hbd z w h).2 hz⟩⟩
  have hm := fun τ => GlobalTheory.T.pair_lattice_degree_bound hG E H D Xo l c Y hgl S₀ Ω K J y 𝔐 (bg τ) (sm τ) (D.p + D.q) (Wb τ) _ nc _ χ
    (hLvb τ) (hWb τ) hbd'
  choose hm hgram using hm
  let Dc : ComponentData II (CMType H) K J Ω (fun τ => ↥(𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ))) :=
    { N := D.p + D.q
      j := j
      two_le_N := by omega
      one_le_j := hj1
      j_le := hj2
      F' := c.F
      finiteDimensional := c.fin
      const := 𝔐.cst
      y := y
      const_mem := fun cc hc r => GlobalTheory.T.constants_in_coord_ratio_field E H D l (Xo l) c Y S₀ Ω K J y 𝔐 cc hc r
      arith := harith
      birational := hbir
      smoothGeneric := GlobalTheory.T.smooth_generic_fibre_of_snc K J Ω y _ bd hsnc
      Bd := mcPts (mCoordIdeal y) ∩ mcPts bd
      bd_subset := Set.inter_subset_left
      bd_closed := hcl
      bd_torus := htor
      bd_conj := hconj
      nCharts := nc
      chart := χ
      chart_cover := hcov'
      W := Wb
      h := hm
      S := S₁
      S_prime := hS₁
      vdeg := vdeg
      vnum := vnum
      vden := vden
      vertical := hvert
      a' := fun _ => 1
      a'_pos := fun _ => one_pos
      A' := A
      A'_deg := funext hAa
      A'_pos := hApos
      A'_conj := hAconj
      KA := 0
      heights := fun W hW _ => by simpa using hAh W hW }
  obtain ⟨Hd, hF⟩ := GlobalTheory.T.component_data_intersection_sum E H D l (Xo l) c Y II K J Ω _ Dc S₀ 𝔐 bg sm
    (fun τ => (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype) s aMu e₀ (fun τ => Subtype.val_injective)
    (fun τ => Submodule.range_subtype _) hne hbgj hr hLvb hWb hli hspan hdeg
  refine ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, _, inferInstance, inferInstance, Dc, Hd,
    { 𝔐 := 𝔐
      deg := deg
      cover := hcov
      bg := bg
      sm := sm
      side := hside
      N_eq := rfl
      i := fun τ => (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype
      i_inj := fun τ => Subtype.val_injective
      i_range := fun τ => Submodule.range_subtype _
      F_eq := hF
      lat := hWb
      bd := hbd'
      metric := fun τ e z w h1 h2 h3 => hgram τ e z w h1 h2 h3
      S_disj := hd
      R_ge := hR
      tors := htors
      ht_vb := hvb
      vert := hvert2 }, hgen, rfl, hj, hbg, hom, hfree⟩

end GlobalTheory.CompanionTheory.Ar
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.full_intersection_generic_bound : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem), IsFullIntersectionSystem II → Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sw : Bool), (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω) (W : CMType H → Type) (_ : ∀ τ, AddCommGroup (W τ)) (_ : ∀ τ, Module Ω (W τ)) (Dc : GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData II (CMType H) K J Ω W) (Hd : GroundTheory.Heights₂.Heights.LowerBoundFree.HodgeData Dc) (Or : CptOrigin Y S₀ Dc Hd), genPt Or.𝔐.ξ₀ = genPt ξ₀ ∧ Dc.S = S₁ ∧ Dc.j = (if sw then D.q else D.p) ∧ Or.bg = (if sw then Sum.inr else Sum.inl) ∧ Or.𝔐.OmVB ∧ ∀ p ∈ S₀ ∪ S₁, HT.HTFree Or.𝔐 p :=
  @GlobalTheory.CompanionTheory.Ar.exists_componentData_origin
end
end
