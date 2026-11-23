module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularChartsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

end GlobalTheory.SiegDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDim

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescAb

theorem abLocus_eq (X S : Scheme.{0}) (j : X ⟶ S) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (hc : ∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁)
      (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧
        ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) :
    abLocus G = Set.range j := by
  ext x
  obtain ⟨R, _, _, ξ, G₁, _, π, hx, hp, hab⟩ := hc x
  have h := abLocus_pullback abLocusOne hG hp.1 (closedPoint R)
  rw [hx] at h
  have h' := hab (closedPoint R)
  rw [hx] at h'
  exact h.trans h'

theorem relDim (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j] (hj : IsDominant j) (A : Over X) [GrpObj A]
    (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom)
    (hG : IsSemiAbelian G) (hpb : IsGrpPullback A G j e) : SmoothOfRelativeDimension g G.hom := by
  have : Smooth G.hom := hG.smooth
  have hopen : IsOpenMap G.hom := G.hom.isOpenMap
  choose n W hW hd using H1.exists_dim G.hom
  have key : ∀ y, n y = g := by
    intro y
    obtain ⟨x, w, hwW, hx⟩ := j.denseRange.exists_mem_open (hopen _ (W y).isOpen) ⟨_, ⟨y, hW y, rfl⟩⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w x hx
    refine H1.dim_base hpb.1 (hd y) hA (hpb.1.isoPullback.inv z) ?_
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    exact hwW
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  rw [← key y]; exact hd y

end GlobalTheory.DescAb

theorem GlobalTheory.DescAb.abLocus_eq_range_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  intro X S j _ hj A _ G _ e g _ hA hG hpb hc
  exact ⟨GlobalTheory.DescAb.abLocus_eq X S j G hG hc, GlobalTheory.DescAb.relDim X S j hj A G e g hA hG hpb⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDimStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.descended_group_abelianLocus_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.DescAb.abLocus_eq_range_and_relDim | exact GlobalTheory.DescAb.abLocus_eq_range_and_relDim | (intros; apply GlobalTheory.DescAb.abLocus_eq_range_and_relDim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt5

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem descSt5 : GlobalTheory.SiegJoin.DescSt5 := by
  intro g _ φ n hn _ F Z z i d S π j _ BD hB hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.descended_group_abelianLocus_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
end
end
end
