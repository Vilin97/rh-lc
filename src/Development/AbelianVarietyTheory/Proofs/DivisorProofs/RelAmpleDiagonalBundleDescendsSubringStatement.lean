module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PolSpread

def good {S : Type} [CommRing S] (B : Over (Sp S)) (M : LB B.left) : Set S :=
  {r | Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))).obj B)
    (M.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))))}

theorem exists_good_notMem {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) (p : Ideal R) [p.IsPrime] :
    ∃ r ∈ good B M, σ r ∉ p := by
  let p₀ : Ideal S := p.comap σ
  have : p₀.IsPrime := Ideal.IsPrime.comap σ
  let a := algebraMap S p₀.ResidueField
  let b := algebraMap R p.ResidueField
  let i : p₀.ResidueField →+* p.ResidueField := Ideal.ResidueField.map p₀ p σ rfl
  have hw : spMap b ≫ spMap σ = spMap i ≫ spMap a := by
    have : i.comp a = b.comp σ := RingHom.ext fun r => Ideal.ResidueField.map_algebraMap p₀ p σ rfl r
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  have hX := (IsPullback.of_hasPullback A.hom (spMap b)).paste_horiz h
  have h₂ : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap b))) (M.pull (pullback.fst A.hom (spMap b) ≫ φ)) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM h hX (spMap b) rfl hL e hA
  rw [hw] at hX
  have h₀ : Out.RelAmple ((Over.pullback (spMap a)).obj B) (M.pull (pullback.fst B.hom (spMap a))) :=
    GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback B.hom (spMap a)) hX
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) h₂
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM a
    (GlobalTheory.FibreAmple.residueField_fraction p₀) h₀
  exact ⟨r, hr', fun hp => hr (Ideal.algebraMap_residueField_eq_zero.2 hp)⟩

theorem span_good {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) : Ideal.span (σ '' good B M) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hm.isPrime
  obtain ⟨r, hr, hr'⟩ := exists_good_notMem σ A B hM hL h e hA m
  exact hr' (hle (Ideal.subset_span ⟨r, hr, rfl⟩))

theorem relAmple_of_span {S S' : Type} [CommRing S] [CommRing S'] (τ : S →+* S') (B : Over (Sp S)) [IsProper B.hom]
    {M : LB B.left} (hM : M.IsLB) (T : Set S) (hT : T ⊆ good B M) (h : Ideal.span (τ '' T) = ⊤) :
    Out.RelAmple (Over.mk (pullback.snd B.hom (spMap τ))) (M.pull (pullback.fst B.hom (spMap τ))) := by
  let f := pullback.snd B.hom (spMap τ)
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have : IsProper f := inferInstance
  have hB := IsPullback.of_hasPullback B.hom (spMap τ)
  refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S') (Over.mk f) _ (pull_isLB hM _) inferInstance inferInstance
    fun s => ?_
  let s' : PrimeSpectrum S' := s
  obtain ⟨r, hr, hs⟩ : ∃ r ∈ T, τ r ∉ s'.asIdeal := by
    by_contra hc
    push_neg at hc
    refine s'.isPrime.ne_top (top_le_iff.1 (h ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨r, hr, rfl⟩
    exact hc r hr
  let U : (Sp S').Opens := PrimeSpectrum.basicOpen (τ r)
  let D : (Sp S).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (U.ι ≫ spMap τ) ⊆ Set.range D.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2
  let u := IsOpenImmersion.lift D.ι (U.ι ≫ spMap τ) hrange
  have hu : u ≫ D.ι = U.ι ≫ spMap τ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hs, ?_⟩
  have hU := (isPullback_morphismRestrict f U).flip
  have a₁ : Out.RelAmple (Over.mk (f ∣_ U)) (M.pull ((f ⁻¹ᵁ U).ι ≫ pullback.fst B.hom (spMap τ))) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback B.hom D.ι) (hU.paste_horiz hB) u hu
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) (hT hr)
  exact GlobalTheory.FibreAmple.relAmple_of_factor (pull_isLB hM _) hU hU (𝟙 _) (Category.id_comp _) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _).symm a₁

end GlobalTheory.CompanionTheory.PolSpread
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleDiagSubring

theorem relAmple_diag_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  intro R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hA₁ hP hP₁ hφ sq e hamp
  classical
  have := hA₁.proper
  have := hA₁.smooth
  let M : LB A₁.left := diagPull A₁ P₁
  have hM : M.IsLB := pull_isLB hP₁ _
  have hL : (diagPull A P).IsLB := pull_isLB hP _
  have e' : LBIso (diagPull A P) (M.pull φ) := GlobalTheory.SiegelPull.diag_iso sq e
  have hspan := GlobalTheory.CompanionTheory.PolSpread.span_good R₁.subtype A A₁ hM hL hφ.1 e' hamp
  have h1 : (1 : R) ∈ Ideal.span (R₁.subtype '' GlobalTheory.CompanionTheory.PolSpread.good A₁ M) := by rw [hspan]; trivial
  obtain ⟨c, hc, hs⟩ := Submodule.mem_span_set.1 h1
  choose! t ht hty using fun y (hy : y ∈ c.support) => hc hy
  refine ⟨c.support.image c, fun R₂ h hF A₂ _ π π₂ hπ sq₂ => ?_⟩
  let τ : R₁ →+* R₂ := Subring.inclusion h
  have hmem : ∀ y ∈ c.support, c y ∈ R₂ := fun y hy =>
    hF (Finset.mem_coe.2 (Finset.mem_image_of_mem c hy))
  have hT : Ideal.span (τ '' (t '' (c.support : Set R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : R₂) = ∑ y ∈ c.support.attach, (⟨c y.1, hmem y.1 y.2⟩ : R₂) * τ (t y.1) := by
      apply Subtype.ext
      refine (OneMemClass.coe_one R₂).trans (hs.symm.trans ?_)
      rw [Finsupp.sum, ← Finset.sum_attach]
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : ((τ (t y.1) : R₂) : R) = y.1 := hty y.1 y.2
      rw [this]
    rw [e1]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨t y.1, ⟨y.1, y.2, rfl⟩, rfl⟩)
  have hB := GlobalTheory.CompanionTheory.PolSpread.relAmple_of_span τ A₁ hM _
    (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy) hT
  have hπ' : Out.RelAmple (Over.mk A₂.hom) (M.pull π) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₁.hom (spMap τ)) hπ.1 (𝟙 _)
      (Category.id_comp _) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hB
  have : IsProper (Over.mk A₂.hom).hom := MorphismProperty.of_isPullback (P := @IsProper) hπ.1 ‹_›
  have hMπ : (M.pull π).IsLB := pull_isLB hM π
  have hL₂ : (diagPull A₂ (P₁.pull π₂)).IsLB := pull_isLB (pull_isLB hP₁ π₂) _
  have e₂ : LBIso (diagPull A₂ (P₁.pull π₂)) (M.pull π) :=
    GlobalTheory.SiegelPull.diag_iso sq₂ (GlobalTheory.lbIso_refl (pull_isLB hP₁ π₂))
  have e₃ : LBIso (M.pull π) ((M.pull π).pull (𝟙 _)) :=
    GlobalTheory.FibreAmple.lbIso_pull_comp (Category.id_comp π).symm (GlobalTheory.lbIso_refl hMπ)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (A := Over.mk A₂.hom) (A' := A₂) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hMπ hL₂
    (LBIso.trans hL₂ hMπ (pull_isLB hMπ _) e₂ e₃) hπ'

end GlobalTheory.AmpleDiagSubring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

theorem _root_.GlobalTheory.T.relAmple_diagonal_bundle_descends_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  first | exact @GlobalTheory.AmpleDiagSubring.relAmple_diag_subring | exact GlobalTheory.AmpleDiagSubring.relAmple_diag_subring | (intros; apply GlobalTheory.AmpleDiagSubring.relAmple_diag_subring <;> assumption)
end
end
