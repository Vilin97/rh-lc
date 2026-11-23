module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairPreimageBaseChangeFstIsBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCoefficientComparisonCommPairPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorSectionsHomBijectiveStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1BijectiveStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pull1RestrictSurjectiveOfComma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpensPreimageBaseChangeIsBasis

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem preAff_basis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ pr _ hsurj
  refine ⟨?_, ?_⟩
  · intro x U hx
    obtain ⟨V, rfl⟩ := hsurj U
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (show pr.base x ∈ V from hx) V.isOpen
    exact ⟨Opposite.op ⟨W, hW⟩, hxW, pr.preimage_mono hWV⟩
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨V, rfl⟩ := hsurj U
    have hmem : pr.base x ∈ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := ⟨⟨h₁, h₂⟩, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open hmem (t₁.unop.1 ⊓ t₂.unop.1 ⊓ V).isOpen
    have hWV' : W ≤ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := hWV
    exact ⟨Opposite.op ⟨W, hW⟩, ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₁.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_left) : W ≤ t₁.unop.1))).op⟩,
      ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₂.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_right) : W ≤ t₂.unop.1))).op⟩, hxW,
      pr.preimage_mono (le_trans hWV' inf_le_right)⟩

end GlobalTheory.Obs.BC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpensPreimageBaseChangeIsBasisStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affineOpensPreimage_baseChange_isBasis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  first | exact @GlobalTheory.Obs.BC.preAff_basis | exact GlobalTheory.Obs.BC.preAff_basis | (intros; apply GlobalTheory.Obs.BC.preAff_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption

end GlobalTheory.SqZeroBC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  first | exact @GlobalTheory.SqZeroBC.preimage_surj | exact GlobalTheory.SqZeroBC.preimage_surj | (intros; apply GlobalTheory.SqZeroBC.preimage_surj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull1Bijective

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisO

theorem restrict_bijective_one : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type)
    [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  intro R _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := BasisExt.hcov_of_basis s G h1
  have hdir := BasisExt.hdir_of_basis s G h2
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

end GlobalTheory.Obs.BasisO
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull1BijectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  first | exact @GlobalTheory.Obs.BasisO.restrict_bijective_one | exact GlobalTheory.Obs.BasisO.restrict_bijective_one | (intros; apply GlobalTheory.Obs.BasisO.restrict_bijective_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtension

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffineHom_of_isPullback {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback hp.flip inferInstance

theorem res_bijective (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] : Function.Bijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 :=
  have H := GlobalTheory.T.affineOpensPreimage_baseChange_isBasis X₀ X₁ pr (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp)
  GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ X₁ s₁ _ (preAff pr) H.1 H.2

theorem tens_bijective {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) [IsAffineHom pr] :
    Function.Bijective (tensCoef hp.w).pull1 := by
  exact GlobalTheory.T.natural_bijective_coefficients_pull1_bijective R₁ _ _ _ _ (tensCoef hp.w).naturality (tensCoef hp.w).smul fun U ↦ GlobalTheory.T.baseChangeTensorSectionsHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop _

def trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CatCoh.H1 (OAff s₁) ≃+ CatCoh.H1 (ext R₁ (OAff s₀)) :=
  haveI := isAffineHom_of_isPullback hp
  (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 (res_bijective q hq hp)).trans
    (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).symm

theorem tens_trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] (c : CatCoh.H1 (OAff s₁)) :
    (tensCoef hp.w).pull1 (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) = (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c :=
  (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).apply_symm_apply _

section Compat

variable {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr] [IsAffineHom pr']
  {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁} (e : f₁ ≫ pr = pr' ≫ f₀)

def pullBC (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preAff pr ⋙ OAff s₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((pairBC pr pr' e).obj p)
  naturality a b := (pairPull h₁).naturality ((pairBC pr pr' e).map a) b
  smul p r b := (pairPull h₁).smul ((pairBC pr pr' e).obj p) r b

def resBC : CoefMap (RingHom.id R₁) (preAff pr' ⋙ OAff t₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end Compat

end GlobalTheory.Obs.BC

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem extendedCoefficients_pullback_compat (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0)
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀}
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀)
    (c : CatCoh.H1 (OAff s₁)) (c' : CatCoh.H1 (OAff t₁))
    (H : IsExtendedPullbackDegOne R₁ h₀ (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) :
    IsPullO h₁ c c' := by
  haveI := isAffineHom_of_isPullback hp
  haveI := isAffineHom_of_isPullback hp'
  have kd := tens_trEquiv q hq hp c
  have kd' := tens_trEquiv q hq hp' c'
  let Φ := CoefMap.restrict (OPair f₁ t₁) (pairBC pr pr' e)
  have inj : Function.Injective Φ.pull1 := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x
    obtain ⟨y', rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x'
    have HH := GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis X₀ X₁ Y₀ Y₁ pr pr' f₀ f₁ e (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp')
    have B := GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ Y₁ t₁ _ (pairBC pr pr' e ⋙ pairFst f₁) HH.1 HH.2
    have k : ∀ z, Φ.pull1 ((pairRes f₁ t₁).pull1 z) =
        (CoefMap.restrict (OAff t₁) (pairBC pr pr' e ⋙ pairFst f₁)).pull1 z := by
      intro z; obtain ⟨z, rfl⟩ := H1.mk_surjective _ z; rfl
    rw [k, k] at hx
    rw [B.1 hx]
  have k1 : Φ.pull1 ((pairPull h₁).pull1 c) = (tensPair hp'.w e).pull1 ((extMap R₁ (pairPull h₀)).pull1
      (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c)) := by
    have a1 : Φ.pull1 ((pairPull h₁).pull1 c) =
        (pullBC e h₁).pull1 ((CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c) := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [a1, ← kd, ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp.w).comp (pullBC e h₁))
      ((extMap R₁ (pairPull h₀)).comp (tensPair hp'.w e)) (𝟙 (pairSnd f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff s₀)) _ b)).trans ?_
    exact GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback R₀ R₁ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' hp.w hp'.w f₀ f₁ h₀ h₁ e p b
  have k2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') = (tensPair hp'.w e).pull1 ((extMap R₁ (pairRes f₀ t₀)).pull1
      (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) := by
    have a2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') =
        (resBC e).pull1 ((CoefMap.restrict (OAff t₁) (preAff pr')).pull1 c') := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c'; rfl
    rw [a2, ← kd', ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp'.w).comp (resBC e))
      ((extMap R₁ (pairRes f₀ t₀)).comp (tensPair hp'.w e)) (𝟙 (pairFst f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff t₀)) _ b)).trans ?_
    have hc : coefHom (pairRes f₀ t₀) p = AlgHom.id R₀ _ := AlgHom.ext fun _ ↦ rfl
    change (tensPair hp'.w e).α p (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = _
    rw [hc]
    exact congrArg ((tensPair hp'.w e).α p) (DFunLike.congr_fun Algebra.TensorProduct.map_id b)
  apply inj
  unfold IsExtendedPullbackDegOne at H
  rw [k1, k2, H]

end GlobalTheory.Obs.BC

theorem GlobalTheory.Obs.BC.extO1 : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' :=
  fun _ _ _ _ _ q hq ↦ ⟨GlobalTheory.Obs.BC.trEquiv q hq, fun _ _ _ _ _ hp _ _ _ _ _ hp' _ _ h₀ h₁ e c c' H ↦
    GlobalTheory.Obs.BC.extendedCoefficients_pullback_compat q hq hp hp' h₀ h₁ e c c' H⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.h1_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' := by
  first | exact @GlobalTheory.Obs.BC.extO1 | exact GlobalTheory.Obs.BC.extO1 | (intros; apply GlobalTheory.Obs.BC.extO1 <;> assumption)
end
end
