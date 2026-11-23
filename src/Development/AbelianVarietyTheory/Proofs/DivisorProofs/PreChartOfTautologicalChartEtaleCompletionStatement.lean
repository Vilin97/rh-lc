module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersi
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Mathlib.RingTheory.TotallySplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  first | exact @GlobalTheory.AbChart.mem_range_of_mem_abLocus | exact GlobalTheory.AbChart.mem_range_of_mem_abLocus | (intros; apply GlobalTheory.AbChart.mem_range_of_mem_abLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpanStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span : ∀ (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (f : R), (Ideal.span {f}).IsRadical → (∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal) → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  first | exact @GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | exact GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl | (intros; apply GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParametersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isRadical_span_prod_relativeRegularParameters : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R) (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  first | exact @GlobalTheory.RelParamRad.isRadical_span_prod | exact GlobalTheory.RelParamRad.isRadical_span_prod | (intros; apply GlobalTheory.RelParamRad.isRadical_span_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.GoodVal

theorem GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  intro g n F S j _ R _ _ _ ξ G₁ _ _ y A₁ _ i₁ β hG hA hB hy p hp
  have : IsNoetherianRing R := inferInstance
  let K := FractionRing R
  by_cases hp0 : p.asIdeal = ⊥
  · have hAprop : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hB.1 F.univ.ab.proper
    refine abLocusOne _ G₁ hG K (jK R) (by rw [← hA.1.isoPullback_inv_snd]; infer_instance) ⟨(⊥ : PrimeSpectrum K), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = p.asIdeal
    rw [hp0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · have := p.isPrime
    obtain ⟨T, hT, gT, hg, hgp⟩ := exists_dvr_centre (K := K) (L := K) p.asIdeal hp0
    have hc : spMap (algebraMap T K) ≫ spMap gT = jK R := by
      rw [← spMap_comp, hg]
    have hginj : Function.Injective gT := by
      refine Function.Injective.of_comp (f := algebraMap T K) ?_
      rw [← RingHom.coe_comp, hg]
      exact (algebraMap K K).injective.comp (IsFractionRing.injective R K)
    have hcl : spMap gT (IsLocalRing.closedPoint T) = p := PrimeSpectrum.ext hgp
    have hr : Set.range (spMap gT ≫ ξ) ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      by_cases hq : q.asIdeal = ⊥
      · have hq' : q = spMap (algebraMap T K) (⊥ : PrimeSpectrum K) := by
          apply PrimeSpectrum.ext
          change q.asIdeal = Ideal.comap (algebraMap T K) ⊥
          rw [hq]; exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective T K)).symm
        refine ⟨y (⊥ : PrimeSpectrum K), ?_⟩
        rw [hq']
        have e : spMap (algebraMap T K) ≫ spMap gT ≫ ξ = y ≫ j := by rw [hy, ← Category.assoc, hc]
        have e' := (congrArg (fun f : Sp K ⟶ S => f (⊥ : PrimeSpectrum K)) e).symm
        first | exact e' | (dsimp only at e'; rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e'; exact e')
      · have hq' : q = IsLocalRing.closedPoint T :=
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime))
        rw [hq']
        have e : (spMap gT ≫ ξ) (IsLocalRing.closedPoint T) = ξ p := by rw [← hcl]; rfl
        rw [e]; exact hp
    haveI := hT
    let yT : Sp T ⟶ F.X := IsOpenImmersion.lift j (spMap gT ≫ ξ) hr
    have hyT : yT ≫ j = spMap gT ≫ ξ := IsOpenImmersion.lift_fac _ _ _
    have hyK : spMap (algebraMap T K) ≫ yT = y := by
      rw [← cancel_mono j, Category.assoc, hyT, ← Category.assoc, hc, hy]
    have hid : IsPullback (𝟙 F.univ.A.left) F.univ.A.hom F.univ.A.hom (𝟙 F.X) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    have := F.univ.ab.smooth
    have := F.univ.ab.proper
    have := F.univ.ab.geomConnected
    obtain ⟨hBs, hB'⟩ := isSemiAbelian_pullback_of_range_subset F.univ.A hid yT (by
      rintro _ ⟨x, rfl⟩; exact ⟨yT x, rfl⟩)
    have hH := IsSemiAbelian.pullback (spMap gT) G₁ hG
    have hPB := ((isGrpPullback_pullback ((Over.pullback yT).obj F.univ.A) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback F.univ.A yT)).congr hyK rfl
    obtain ⟨a, ha, -⟩ := grpPullback_iso hPB hB
    have hPG := ((isGrpPullback_pullback ((Over.pullback (spMap gT)).obj G₁) (spMap (algebraMap T K))).comp
      (isGrpPullback_pullback G₁ (spMap gT))).congr hc rfl
    obtain ⟨b, hb, -⟩ := grpPullback_iso hA hPG
    have hE : IsMonHom (a ≪≫ b).hom := inferInstanceAs (IsMonHom (a.hom ≫ b.hom))
    obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hBs hH (a ≪≫ b).hom hE
    obtain ⟨Ψ, ⟨-, hΨ⟩, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr T K _ _ hH hBs (a ≪≫ b).inv inferInstance
    have hx := (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G₁ (spMap gT)).1
      (IsLocalRing.closedPoint T)).2 (abLocus_subset_of_extends hBs hH _ Φ Ψ hΦ hΨ (hB' _))
    rw [hcl] at hx
    exact hx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  first | exact @GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | exact GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | (intros; apply GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdEqChart

theorem boundary_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → ∀ (m : ℕ) (t : Fin m → R), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ k, t k} := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy hrad m t ht hab
  have key : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal := fun p =>
    ⟨fun h => (hab p).1 (GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart g n F S j R ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p h),
     fun h => GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion g n F S j R b ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p ((hab p).2 h)⟩
  refine ⟨key, GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span S j.opensRange R ξ _ (GlobalTheory.T.isRadical_span_prod_relativeRegularParameters _ R b m t ht) (fun p => ?_) hrad⟩
  rw [Scheme.Hom.coe_opensRange]
  exact key p

end GlobalTheory.BdEqChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartPre

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem eq_of_jK_comp_eq {R o : Type} [CommRing R] [IsDomain R] [CommRing o] {u v : Sp R ⟶ Sp o}
    (h : jK R ≫ u = jK R ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  have h' : u ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = v ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  congr 1
  ext a
  exact IsFractionRing.injective R (FractionRing R) (congrArg (fun f => f.hom a) h')

theorem preChart_of_isEtaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  intro g hg φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy het hfu
  obtain ⟨J, -, -, -, -, hP, -, hji, -, -, hval⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hM
  obtain ⟨hsa, hab, hgen, hmum, hbase⟩ := hF
  obtain ⟨hreg, hch, -, -, hrel, -⟩ := GlobalTheory.TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, -⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  haveI : IsProper (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : S.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ z)]
    infer_instance⟩
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hc : IsAdicComplete (maximalIdeal C.R) C.R := C.compl.2.1
  have hξ : ξ ≫ π ≫ z = spMap C.b := eq_of_jK_comp_eq (by
    rw [← hbase, ← Category.assoc, ← hy, Category.assoc, ← Category.assoc j, hji, hiz])
  have hrad := GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ (Scheme.stalkClosedPointTo ξ).hom hc het hfu
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.BdEqChart.boundary_eq g n F S j C.R C.b ξ G₁ y ((Over.pullback (jK C.R)).obj G₁)
    (pullback.fst G₁.hom (jK C.R)) α₁ hsa (isGrpPullback_pullback G₁ (jK C.R)) hgen hy hrad C.m C.t hrel hab
  haveI : Module.Free ℤ C.Q.X := Module.Free.of_equiv C.e.toIntLinearEquiv.symm
  have hnat : ∀ k, ∃ c : ℕ, φ.evalZ ((n : ℤ) • C.δ k) = c := fun k =>
    (hφ C.Q.X hrk).exists_nat (Submodule.smul_mem _ _ (hcone.mem k)) fun w =>
      mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
  choose c hcn using hnat
  have ha : ∀ k, ((d * c k : ℕ) : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := fun k => by rw [hcn, Nat.cast_mul]
  have hBD := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F S j φ hφ d BD.idealSheaf hval C.R hc C.b ξ C.Q G₁ y α₁ hsa hgen
    hy.symm hmum C.m C.t C.δ (fun k => d * c k) hrel hab hcone hdef hmono ha
  exact ⟨C.R, inferInstance, hreg, inferInstance, C.b, ξ, C.m, C.t, C.Q, C.δ, fun k => d * c k, G₁, inferInstance, y, α₁,
    ⟨hc, hch, hξ, rfl, het, hfu⟩, ⟨hrel, hb₂, hb₁⟩, ⟨hsa, hab, hy, hgen⟩, ⟨hmum, hrk, hcone, hdef, hmono⟩, ha, hBD⟩

end GlobalTheory.TChartPre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.preChart_of_tautologicalChart_etaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  first | exact @GlobalTheory.TChartPre.preChart_of_isEtaleCompletion | exact GlobalTheory.TChartPre.preChart_of_isEtaleCompletion | (intros; apply GlobalTheory.TChartPre.preChart_of_isEtaleCompletion <;> assumption)
end
end
