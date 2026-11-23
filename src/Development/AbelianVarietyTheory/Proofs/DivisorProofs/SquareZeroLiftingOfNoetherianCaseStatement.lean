module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCaseStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGeneratedStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k : GrpMor (dp0 S) (𝟙 (Sp S)) AS (divided₂ h) (spMap π) A₀ σ
        (spMap ι₀ ≫ spMap πS) (ψA ≫ iS) := GrpMor.of_isGrpPullback (IsDPMorphism.comp _ mA.dp (liftMor (divided₂ hJ) hAS).dp) (by simpa using hbase) (IsGrpPullback.comp hψA hAS)
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.push_mem_liftFil_of_injective_alt : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  first | exact @GlobalTheory.SqLift.push_mem_liftFil_of_injective | exact GlobalTheory.SqLift.push_mem_liftFil_of_injective | (intros; apply GlobalTheory.SqLift.push_mem_liftFil_of_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherian

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftHom_exists_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  intro P H R _ I h R₀ _ π hπ hker g A₀ _ A _ i hA abA smA g' B₀ _ B _ j hB abB smB f₀ _ hfil
  obtain ⟨S, ι₀, AS₀, _, AS, _, iS, BS₀, _, BS, _, jS, fS₀, φA, φB, ψA, ψB, hfg, hι, _, hAS, hBS, abAS, smAS,
    abBS, smBS, pA, pB, qA, qB, cA, cB, cf⟩ := GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated R I R₀ π hπ hker g A₀ A i hA abA smA g' B₀ B j hB abB smB f₀
  have hS : (I.comap S.subtype) ^ 2 = 0 := by
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    refine (Ideal.le_comap_pow _ 2).trans ?_
    rw [h, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hfilS := GlobalTheory.T.push_mem_liftFil_of_injective_alt P R I h R₀ π hπ hker S S.subtype Subtype.val_injective (I.comap S.subtype) hS
    (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ι₀ hι
    g A₀ A i hA AS₀ AS iS hAS abA smA abAS smAS φA ψA pA qA cA
    g' B₀ B j hB BS₀ BS jS hBS abB smB abBS smBS φB ψB pB qB cB f₀ fS₀ cf hfil
  obtain ⟨fS, ⟨_, efS⟩, -⟩ := (H S (I.comap S.subtype) hS (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker).2 g AS₀ AS iS hAS abAS smAS g' BS₀ BS jS hBS abBS smBS fS₀ hfilS
  let fl : A.left ⟶ B.left := pB.1.lift (φA ≫ fS.left) A.hom (by
    rw [Category.assoc, Over.w fS, pA.1.w])
  refine ⟨Over.homMk fl (pB.1.lift_snd _ _ _), ?_⟩
  apply pB.1.hom_ext
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_fst]
    rw [reassoc_of% cA, efS, ← Category.assoc, ← cf, Category.assoc, cB]
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_snd]
    rw [hA.1.w, hB.1.w, ← Category.assoc, Over.w f₀]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherianStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftHom_exists_of_noetherian_alt : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.liftHom_exists_of_noetherian | exact GlobalTheory.liftHom_exists_of_noetherian | (intros; apply GlobalTheory.liftHom_exists_of_noetherian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCase

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem sqLifting_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  intro P H R _ I h R₀ _ π hπ hI
  refine ⟨GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case P H R I h R₀ π hπ hI, ?_⟩
  intro g A₀ _ A _ i hA hAa hg g' B₀ _ B _ j hB hBa hg' f₀ _ hf
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.liftHom_exists_of_noetherian_alt P H R I h R₀ π hπ hI g A₀ A i hA hAa hg g' B₀ B j hB hBa hg' f₀ hf
  exact GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, by rw [hI]; exact h⟩ A₀ B₀ A B i j hA hB hAa hBa f₀ φ hφ

end GlobalTheory.SqLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCaseStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.squareZeroLifting_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  first | exact @GlobalTheory.SqLift.sqLifting_of_noetherian | exact GlobalTheory.SqLift.sqLifting_of_noetherian | (intros; apply GlobalTheory.SqLift.sqLifting_of_noetherian <;> assumption)
end
end
