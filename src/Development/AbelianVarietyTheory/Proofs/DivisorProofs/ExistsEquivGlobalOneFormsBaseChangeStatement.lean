module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimagStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamily

section

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg
  set I : Ideal R := LinearMap.ker g with hIdef
  have hI : I ≠ ⊤ := by
    intro hT
    have h1 : (1 : R) ∈ I := hT ▸ Submodule.mem_top
    rw [hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx h1
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  obtain ⟨i, hi⟩ := hmax m hm
  let e : (R ⧸ I) →ₗ[R] M := (LinearMap.ker g).liftQ g le_rfl
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hinj : Function.Injective (e.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  haveI := h i
  haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton
  haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton
  haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton
  have htop : I • (⊤ : Submodule R (B i)) = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
  exact hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))

theorem bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamilyStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  first | exact @GlobalTheory.bijective_of_lTensor_flat_family | exact GlobalTheory.bijective_of_lTensor_flat_family | (intros; apply GlobalTheory.bijective_of_lTensor_flat_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTop

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTopStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.exists_affineOpen_map_maximal_proper : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  first | exact @GlobalTheory.PointSec.exists_affine_map_ne_top | exact GlobalTheory.PointSec.exists_affine_map_ne_top | (intros; apply GlobalTheory.PointSec.exists_affine_map_ne_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.CechDR

theorem flat_sec (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (hs : Flat s')
    (U : X'.affineOpens) : Module.Flat R' (Sec s' U.1) := by
  have h1 : (s'.appLE ⊤ U.1 le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) s' hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h2 : (secMap s' U.1).hom.Flat := by
    exact RingHom.Flat.comp h0 h1
  exact h2

end GlobalTheory.CechDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme : ∀ (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R'), Flat s' → ∀ U : X'.affineOpens, Module.Flat R' (Sec s' U.1) := by
  first | exact @GlobalTheory.CechDR.flat_sec | exact GlobalTheory.CechDR.flat_sec | (intros; apply GlobalTheory.CechDR.flat_sec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (GlobalTheory.T.exists_affineOpen_map_maximal_proper R' X X' s' φ hsu)
      (fun U ↦ GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_equiv_globalOneForms_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | exact GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | (intros; apply GlobalTheory.AbCoh.exists_equiv_globForm_baseChange <;> assumption)
end
end
