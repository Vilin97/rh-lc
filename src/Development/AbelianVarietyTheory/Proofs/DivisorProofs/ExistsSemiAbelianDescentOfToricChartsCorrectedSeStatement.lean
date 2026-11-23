module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPartStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularChartsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Mathlib.RingTheory.MvPowerSeries.Equiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundarStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  first | exact @GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | exact GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | (intros; apply GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  first | exact @GlobalTheory.SemiAbDesc.exists_grpPullback_map | exact GlobalTheory.SemiAbDesc.exists_grpPullback_map | (intros; apply GlobalTheory.SemiAbDesc.exists_grpPullback_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTriple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem genOf_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  intro E _ _ _ H Dw l Xo c R _ _ y t tF hy mF
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  obtain ⟨b⟩ := GlobalTheory.TraitOrder.cancel rfl mF m₂
  obtain ⟨e, he, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso (isGrpPullback_pullback t.G (jK R)) m₁.cart
  haveI := he
  exact ⟨e.hom.left ≫ b.φ,
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso e).comp b.cart).congr (Category.id_comp _) rfl⟩

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTripleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  first | exact @GlobalTheory.UPoinc.genOf_isGrpPullback | exact GlobalTheory.UPoinc.genOf_isGrpPullback | (intros; apply GlobalTheory.UPoinc.genOf_isGrpPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTriple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAmpleXF

theorem relAmple_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)) :
    SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  intro mF
  have hP : IsProper tF.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper
  obtain ⟨w, hw, -⟩ := mF.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ tF.G tF.PP.L tF.PP.isLB inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤)
    (x := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) s) trivial
  let f := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let U := f ⁻¹ᵁ V
  refine ⟨U, hs, ?_⟩
  have H : IsPullback ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (tF.G.hom ∣_ U) Xo.univ.t.G.hom (U.ι ≫ f) :=
    (isPullback_morphismRestrict tF.G.hom U).flip.paste_horiz mF.cart.1
  obtain ⟨w', hw'⟩ : LBIso (tF.PP.L.pull (tF.G.hom ⁻¹ᵁ U).ι) (Xo.univ.t.PP.L.pull ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ)) :=
    LBIso.chartPull (chartPullPull _ _)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => (tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (fun _ => mF.φ) (fun _ => 1)
        (tF.G.hom ⁻¹ᵁ U).ι fun _ => rfl) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (tF.G.hom ∣_ U)) H Xo.univ.t.PP.isLB (pull_isLB tF.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) Xo.univ.ample

end GlobalTheory.PullAmpleXF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTripleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  first | exact @GlobalTheory.PullAmpleXF.relAmple_XF | exact GlobalTheory.PullAmpleXF.relAmple_XF | (intros; apply GlobalTheory.PullAmpleXF.relAmple_XF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartDesc

theorem exists_semiAbelian_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP hpre tF mF
  have hNoeth : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP.2.2.2.2.1.2.1
  have hNorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).1 hP.2.2.2.2.1.1.1
  have hdom : IsDominant j := ⟨hP.2.2.2.2.1.2.2.2.1⟩
  have hAab : IsAbelianScheme tF.G :=
    ⟨tF.comm, tF.semi.smooth, MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper, tF.semi.geomConnected⟩
  have hLB : tF.PP.L.IsLB := tF.PP.isLB
  have hAmp : RelAmple tF.G tF.PP.L := GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple Xo c tF mF
  have hkc : ∀ (k : Type) [Field k], IsAdicComplete (maximalIdeal k) k := fun k _ => by
    rw [maximalIdeal_eq_bot]; infer_instance

  have bdChart : ∀ (x : S) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e))
      (ξ : Sp (ChartRing k m e) ⟶ S), C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) = x →
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ∃ Ch : GlobalTheory.Desc.Chart j tF.G x, ∀ (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ π : Ch.G.left ⟶ G.left,
        IsGrpPullback Ch.G G Ch.ξ π → (x ∈ abLocus G ↔ closedPoint (ChartRing k m e) ∈ abLocus C.t.G) := by
    intro x k _ m e C ξ hy hcl het
    haveI : CharZero (ChartRing k m e) := charZero_of_injective_ringHom C.b.injective
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    haveI := hkc k
    obtain ⟨α, hα⟩ := GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple Xo c (ChartRing k m e) C.y C.t tF C.gen mF
    refine ⟨{ R := ChartRing k m e
              complete := GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
              charZero := inferInstance
              ξ := ξ
              centre := hcl
              etc := het
              unr := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ het
              G := C.t.G
              semi := C.t.semi
              y := C.y
              hy := hy
              α := α
              gen := hα }, ?_⟩
    intro G _ hG π hπ
    rw [← hcl]
    exact abLocus_pullback abLocusOne hG hπ.1 (closedPoint _)
  have hch : ∀ x : S, Nonempty (GlobalTheory.Desc.Chart j tF.G x) := by
    intro x
    by_cases hx : x ∈ Set.range j
    · exact GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart Xo c j tF.G tF.semi x hx
    · obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, -⟩ := hpre x hx
      obtain ⟨Ch, -⟩ := bdChart x k m e C ξ hy hcl het
      exact ⟨Ch⟩
  obtain ⟨G, _, e, hG, hpb, hmap⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts (Xo.XF c) S hNorm j hdom tF.G hAab tF.PP.L hLB hAmp hch
  haveI : IsCommMonObj G := hG.comm
  refine ⟨G, inferInstance, hG.comm, e, hG, hpb, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_contra hxj
      obtain ⟨k, _, m, e', C, ξ, a, htaut, hy, hcl, het, -, hset, -⟩ := hpre x hxj
      obtain ⟨Ch, hCh⟩ := bdChart x k m e' C ξ hy hcl het
      obtain ⟨π', hπ', -⟩ := hmap x Ch
      have hcp := (hCh G hG π' hπ').1 hx
      have hprod : ∏ i, C.s i ∈ (closedPoint (ChartRing k m e')).asIdeal := by
        by_contra hn
        exact hxj (hcl ▸ (hset _).2 hn)
      have hm : 1 ≤ C.m := by
        rcases Nat.eq_zero_or_pos C.m with h0 | h0
        · exfalso
          haveI : IsEmpty (Fin C.m) := by rw [h0]; infer_instance
          rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
          exact (maximalIdeal (ChartRing k m e')).ne_top_iff_one.1 (maximalIdeal.isMaximal _).ne_top hprod
        · exact h0
      exact GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart Xo c φ k m e' C htaut hm hcp
    · rintro ⟨x', rfl⟩
      rw [abLocus_pullback abLocusOne hG hpb.1 x']
      intro K _ _ t _
      haveI := hAab.proper
      infer_instance
  · intro k _ m n C hC ξ hξ tK a b
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
    haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).2
    exact GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain (ChartRing k m n) j tF.G G e hG hpb C.t.G C.t.semi ξ C.y hξ tK.G a.φ b.φ a.cart b.cart

theorem exists_semiAbelian_of_charts_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP _ hpre tF mF
  exact exists_semiAbelian_of_charts Xo c φ hpq hfan hnsi zs i OZ N d J π j BD hP hpre tF mF

end GlobalTheory.UChartDesc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  first | exact @GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | exact GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | (intros; apply GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB <;> assumption)
end
end
