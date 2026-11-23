module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationBlowupPullbackFiniteCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntOfIntegralSchemeGenericPointStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.eq_of_specializes_same_fibre_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  first | exact @GlobalTheory.eq_of_specializes_of_isIntegralHom | exact GlobalTheory.eq_of_specializes_of_isIntegralHom | (intros; apply GlobalTheory.eq_of_specializes_of_isIntegralHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDefinedOverSubfieldOfIsIntegralHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefOverIntegral

theorem mem_of_isIntegral {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K}
    (hx : IsIntegral k₀ x) : x ∈ k₀ := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k₀)
    (K := integralClosure k₀ K)).2 ⟨x, hx⟩
  have h1 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = x := congrArg Subtype.val ha
  have h2 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = (a : K) := rfl
  rw [← h1, h2]
  exact a.2

theorem defOver_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K]
    (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  intro X Y f _ K _ k₀ hk P ⟨Q₀, hQ⟩
  let g := pullback.snd f Q₀
  let Pt : Sp K ⟶ pullback f Q₀ := pullback.lift P (spMap k₀.subtype) hQ.symm
  haveI : IsAffine (pullback f Q₀) := isAffine_of_isAffineHom g
  have hint : (g.app ⊤).hom.IsIntegral := g.isIntegral_app ⊤ (isAffineOpen_top _)
  let φc : Γ(pullback f Q₀, ⊤) ⟶ CommRingCat.of K := Pt.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hPt : Pt = Spec.map φc ≫ (pullback f Q₀).isoSpec.inv := by
    have h := Scheme.isoSpec_inv_naturality Pt
    rw [Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg : Pt ≫ g = spMap k₀.subtype := pullback.lift_snd _ _ _
  have hcomp : g.appTop ≫ φc = (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom ≫ CommRingCat.ofHom k₀.subtype := by
    have h := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at h
    simp only [φc, ← Category.assoc, h]
    exact Scheme.ΓSpecIso_naturality _
  have hmem : ∀ r, φc.hom r ∈ k₀ := by
    intro r
    obtain ⟨p, hpm, hp⟩ := hint r
    refine mem_of_isIntegral k₀ hk ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap k₀ K).comp (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom = φc.hom.comp (g.app ⊤).hom := by
      have := congrArg CommRingCat.Hom.hom hcomp
      exact this.symm
    rw [e]
    have h3 := Polynomial.hom_eval₂ p (g.app ⊤).hom φc.hom r
    rw [hp] at h3
    exact h3.symm.trans (RingHom.map_zero _)
  let φ₀ : Γ(pullback f Q₀, ⊤) →+* k₀ := φc.hom.codRestrict k₀ hmem
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (pullback f Q₀).isoSpec.inv ≫ pullback.fst f Q₀, ?_⟩
  have e2 : spMap k₀.subtype ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map φc := by
    rw [spMap, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, e2, ← Category.assoc, ← hPt]
  exact pullback.lift_fst _ _ _

end GlobalTheory.DefOverIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDefinedOverSubfieldOfIsIntegralHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.pointDefinedOverSubfield_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  first | exact @GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom | exact GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom | (intros; apply GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepCov

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  intro E _ _ _ H Dw _ l Xo c C J hJi S π hNB M _ g z₁ ζ hcov
  obtain ⟨hMn, ⟨U, g', hg'fin, hg'U, hUF⟩, hζ, hgen⟩ := hcov
  haveI := hg'fin
  haveI := C.ft
  haveI : Algebra.FiniteType ℤ (CommRingCat.of C.o) := ‹Algebra.FiniteType ℤ C.o›
  haveI : IsNoetherianRing C.o := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI := C.iF_open
  obtain ⟨Z', b, hB, hBproj, -⟩ := GlobalTheory.ProjBlowup.exists_blowup C.z C.proj J
  haveI : IsProper C.z := by
    obtain ⟨m, e, he, he'⟩ := C.proj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper (b ≫ C.z) := by
    obtain ⟨m, e, he, he'⟩ := hBproj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b C.z
  obtain ⟨-, S₀, π₀, ν, -, hB₀, hνπ, -, -, -, -⟩ := hNB
  obtain ⟨ψ₀, hψ₀, -⟩ := hB.2 S₀ (π₀ ≫ pullback.fst C.z (spMap C.b))
    (by rw [Scheme.IdealSheafData.comap_comp]; exact hB₀.1)
  have hψU : Set.range ψ₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show b (ψ₀ s) ∈ U
    rw [← Scheme.Hom.comp_apply, hψ₀, Scheme.Hom.comp_apply]
    exact hUF ⟨_, rfl⟩
  let ψU : S₀ ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι ψ₀ hψU
  have hψUf : ψU ≫ (b ⁻¹ᵁ U).ι = ψ₀ := IsOpenImmersion.lift_fac _ _ _
  have hψUb : ψU ≫ (b ∣_ U) ≫ U.ι = π₀ ≫ pullback.fst C.z (spMap C.b) := by
    rw [morphismRestrict_ι, ← Category.assoc, hψUf, hψ₀]
  have hpt : ∀ q : Sp (M.presheaf.stalk z₁), g (M.fromSpecStalk z₁ q) = pullback.fst C.z (spMap C.b) (ζ q) := by
    intro q
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hζ]
  haveI := hMn
  haveI : IsDomain (M.presheaf.stalk z₁) := inferInstance
  let p0 : Sp (M.presheaf.stalk z₁) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y0, hy0⟩ := hgen p0 rfl
  let m0 : M := M.fromSpecStalk z₁ p0
  have hm0 : g m0 = C.i y0 := by
    rw [hpt, ← hy0]; rfl
  have hgm : ∀ m, g m ∈ Set.range C.i → (g' ≫ U.ι) m ∉ J.support := by
    intro m ⟨y, hy⟩ hJ
    rw [hg'U] at hJ
    exact hJi _ hJ ⟨y, hy⟩
  have hm0J : (g' ≫ U.ι) m0 ∉ J.support := hgm m0 ⟨y0, hm0.symm⟩
  obtain ⟨S₁, hS₁i, p₁, ν₁, hS₁n, hp₁P, hν₁fin, hcomm, hEff, hrange, hlift⟩ :=
    GlobalTheory.T.exists_normalisation_blowup_pullback_finiteCover (o := CommRingCat.of C.o) C.z b J hB U g' ⟨m0, hm0J⟩
  haveI := hν₁fin

  haveI : IsPreimmersion (spMap C.b) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  obtain ⟨W', hW'o, hW'⟩ := ((IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).isInducing.isOpen_iff).mp
    C.iF.isOpenMap.isOpen_range
  let sM : M ⟶ Sp ℤ := g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))
  obtain ⟨x0, hx0⟩ := hrange m0 hm0J
  haveI hSpecZ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine ⟨S₁, hS₁i, p₁, sM, (p₁ ≫ g) ⁻¹ᵁ ⟨W', hW'o⟩, ?_, ?_, ?_, hS₁n, hp₁P, ?_, ?_, ?_, ?_, ?_⟩
  · show LocallyOfFiniteType (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · show QuasiCompact (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    haveI : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · apply GlobalTheory.T.flat_int_of_integral_scheme_generic_point _ x0
    have eM : C.i ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)) =
        (C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) := by
      simp only [UCompact.i, Category.assoc, pullback.condition_assoc]
      rw [← Spec.map_comp]; rfl
    have e : (p₁ ≫ sM) x0 = Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0) := by
      rw [← Scheme.Hom.comp_apply, ← eM]
      show (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) (g (p₁ x0)) = _
      rw [hx0, hm0]
      rfl
    rw [e]
    show Ideal.comap _ _ = ⊥
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).isPrime
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).asIdeal), Ideal.comap_bot_of_injective]
    exact fun u v h => Int.cast_injective (α := c.F) (by simpa using h)
  · constructor
    have hVo : IsOpen {m : M | (g' ≫ U.ι) m ∉ J.support} :=
      (g' ≫ U.ι).continuous.isOpen_preimage _ J.support.isClosed.isOpen_compl
    exact (hVo.dense ⟨m0, hm0J⟩).mono fun m hm => hrange m hm
  · rw [← hg'U]; exact hEff
  · refine ⟨x0, ?_⟩
    show g (p₁ x0) ∈ W'
    rw [hx0, hpt]
    show ζ p0 ∈ pullback.fst C.z (spMap C.b) ⁻¹' W'
    rw [hW']; exact ⟨y0, hy0⟩
  · intro K _ x ev hx hxU
    have hr : Set.range (spMap ev ≫ ζ) ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      rw [← hW']
      show pullback.fst C.z (spMap C.b) (ζ (spMap ev w)) ∈ W'
      rw [← hpt, ← Scheme.Hom.comp_apply (spMap ev), ← hx, Scheme.Hom.comp_apply]
      exact hxU ⟨w, rfl⟩
    exact ⟨IsOpenImmersion.lift C.iF _ hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro R _ _ _ _ a ev ha hgR
    let β : Sp R ⟶ M := spMap ev ≫ M.fromSpecStalk z₁
    have hβg : β ≫ g = a ≫ π ≫ pullback.fst C.z (spMap C.b) := by
      simp only [β, Category.assoc, ← hζ]
      rw [← Category.assoc a π, ha, Category.assoc]
    have hab : (a ≫ ν ≫ ψU) ≫ (b ∣_ U) = β ≫ g' := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hψUb, Category.assoc, hg'U, hβg,
        ← hνπ, Category.assoc]
    have hgw : ∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support := by
      intro w
      have e : jK R ≫ β ≫ g' ≫ U.ι = (jK R ≫ a ≫ π) ≫ pullback.fst C.z (spMap C.b) := by
        rw [hg'U, hβg]; simp only [Category.assoc]
      rw [e]
      obtain ⟨y, hy⟩ := hgR ⟨w, rfl⟩
      intro hJ
      refine hJi _ hJ ⟨y, ?_⟩
      show _ = pullback.fst C.z (spMap C.b) ((jK R ≫ a ≫ π) w)
      rw [← hy]; rfl
    obtain ⟨ξ₁, hξν, hξp⟩ := hlift R (a ≫ ν ≫ ψU) β hab hgw
    refine ⟨ξ₁, hξp, ?_⟩
    intro K _ _ ev' k₀ hk₀ hcl hdef
    refine ⟨fun p => ?_, ?_⟩
    · have e1 : ∀ t, ν₁ (ξ₁ t) = ψU (ν (a t)) := fun t => by
        rw [← Scheme.Hom.comp_apply, hξν]; rfl
      apply GlobalTheory.T.eq_of_specializes_same_fibre_isIntegralHom ν₁
      · exact (IsLocalRing.specializes_closedPoint _).map ξ₁.continuous
      · have e2 := e1 (closedPoint R)
        have e3 : a ((spMap ev') p) = a (closedPoint R) := hcl p
        rw [Scheme.Hom.comp_apply, e1, e3]
        exact e2.symm
    · apply GlobalTheory.T.pointDefinedOverSubfield_of_isIntegralHom ν₁ k₀ hk₀
      obtain ⟨P₀, hP₀⟩ := hdef
      refine ⟨P₀ ≫ ν ≫ ψU, ?_⟩
      simp only [Category.assoc, hξν]
      rw [reassoc_of% hP₀]

end GlobalTheory.USepCov
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  first | exact @GlobalTheory.USepCov.exists_cover | exact GlobalTheory.USepCov.exists_cover | (intros; apply GlobalTheory.USepCov.exists_cover <;> assumption)
end
end
