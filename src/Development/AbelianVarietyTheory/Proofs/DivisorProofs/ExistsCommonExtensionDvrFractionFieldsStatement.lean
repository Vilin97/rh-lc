module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecompleteOfPowLe

section

@[expose] public section

noncomputable section

open IsLocalRing

namespace GlobalTheory.FiniteCompletionLocalHom

theorem isLocalHom_of_finite {R R₂ V : Type*} [CommRing R] [IsLocalRing R] [CommRing R₂] [IsLocalRing R₂]
    [CommRing V] [IsLocalRing V] (ρ : R →+* R₂) (hρ : ρ.Finite) (ψ : R₂ →+* V)
    (h : IsLocalHom (ψ.comp ρ)) : IsLocalHom ψ := by
  letI := ρ.toAlgebra
  haveI : Module.Finite R R₂ := hρ
  haveI : Algebra.IsIntegral R R₂ := Algebra.IsIntegral.of_finite R R₂

  have hc : (maximalIdeal V).comap (ψ.comp ρ) = maximalIdeal R :=
    ((IsLocalRing.local_hom_tfae (ψ.comp ρ)).out 1 5).mp h
  have hP : ((maximalIdeal V).comap ψ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    have hc' : ((maximalIdeal V).comap ψ).comap (algebraMap R R₂) = maximalIdeal R := hc
    change (((maximalIdeal V).comap ψ).comap (algebraMap R R₂)).IsMaximal
    rw [hc']
    infer_instance
  exact ((IsLocalRing.local_hom_tfae ψ).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hP)

theorem exists_extension : ∀ (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), IsLocalHom φ →
    ∀ (ρ : R →+* R₂), RingHom.Finite ρ → ∀ (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω) (m : R₂ →+* Ω),
    Function.Injective m → (∀ r : R, m (ρ r) = j (algebraMap W (FractionRing W) (φ r))) →
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ GlobalTheory.Mum.FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧
      (∀ w : W, j₂ (algebraMap W₂ (FractionRing W₂) (σ w)) = j (algebraMap W (FractionRing W) w)) ∧
      ∀ r : R₂, j₂ (algebraMap W₂ (FractionRing W₂) (φ₂ r)) = m r := by
  intro R R₂ W _ _ _ _ _ _ _ _ _ hW φ hφ ρ hρ Ω _ j m hm hcomp
  obtain ⟨hdvr, hcompl, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).mp hW
  haveI := hdvr
  haveI := hcompl
  haveI := hchar
  letI : Algebra (FractionRing W) Ω := j.toAlgebra
  letI : Algebra W Ω := (j.comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  obtain ⟨s₀, hs₀int, hs₀⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ m (fun r => hcomp r)
  have hmint : ∀ r, IsIntegral W (m r) := fun r =>
    hs₀ (integralClosure W Ω) (fun x hx => hs₀int x hx) r

  let F : IntermediateField (FractionRing W) Ω := algebraicClosure (FractionRing W) Ω
  have hmF : ∀ r, m r ∈ F := fun r =>
    ((hmint r).tower_top : IsIntegral (FractionRing W) (m r))
  letI : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic W F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing W)).mpr inferInstance
  haveI : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).mpr
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W (FractionRing W)))
  let mF : R₂ →+* F := m.codRestrict F hmF
  obtain ⟨s, hsint, hs⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ mF (fun r => Subtype.ext (hcomp r))

  obtain ⟨W', hdvr', hc₁, -, hfin, -, hloc, -, hmem⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra W F s
  haveI := hdvr'
  have hWs : ∀ a, mF a ∈ W' := hs W' fun x hx => hmem x hx (hsint x hx)
  let φ₂ : R₂ →+* W' := mF.codRestrict W' hWs
  let σ : W →+* W' := algebraMap W W'
  have hσinj : Function.Injective σ := fun a b hab =>
    FaithfulSMul.algebraMap_injective W F (congrArg Subtype.val hab)
  let ι : W' →+* Ω := (algebraMap F Ω).comp (algebraMap W' F)
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  let j₂ : FractionRing W' →+* Ω := IsFractionRing.lift hιinj
  have hC : GlobalTheory.LN.CDvr W' :=
    (GlobalTheory.LN.cDvr_iff W').mpr ⟨hdvr', hc₁, charZero_of_injective_algebraMap hσinj⟩
  have hcomm : φ₂.comp ρ = σ.comp φ := RingHom.ext fun r => Subtype.ext (Subtype.ext (hcomp r))
  haveI : IsLocalHom σ := hloc
  have hloc₂ : IsLocalHom (φ₂.comp ρ) := by
    rw [hcomm]
    exact RingHom.isLocalHom_comp σ φ
  refine ⟨W', inferInstance, inferInstance, inferInstance, σ, φ₂, j₂, hC,
    (⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hC, hσinj, RingHom.finite_algebraMap.mpr hfin⟩ : _ ∧ _ ∧ _),
    hloc, fun a b hab => hm (congrArg (fun x : W' => ((x : F) : Ω)) hab),
    isLocalHom_of_finite ρ hρ φ₂ hloc₂, hcomm, fun w => IsFractionRing.lift_algebraMap hιinj (σ w),
    fun r => IsFractionRing.lift_algebraMap hιinj (φ₂ r)⟩

end GlobalTheory.FiniteCompletionLocalHom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FieldTraitExt

theorem exists_normalization (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (K' : Type) [Field K'] (io : FractionRing R →+* K') (hio : io.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂)
      (e : R₂ →+* K'), FinExt ρ ∧ Function.Injective e ∧ (∀ r, e (ρ r) = io (algebraMap R _ r)) ∧
      ∀ y, i (e y) = algebraMap R₂ _ y := by
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hchar⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hio
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let R₂ := integralClosure R K'
  haveI hfin : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) K' R₂
  haveI : IsLocalRing R₂ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) R₂
  haveI : IsFractionRing R₂ K' := IsIntegralClosure.isFractionRing_of_finite_extension R (FractionRing R) K' R₂
  have hRK : Function.Injective (algebraMap R K') := io.injective.comp (IsFractionRing.injective R _)
  have hinj : Function.Injective (algebraMap R R₂) := fun x y h => hRK (congrArg Subtype.val h)
  haveI : IsNoetherianRing R₂ := IsNoetherianRing.of_finite R R₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algebraMap R R₂,
    (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).toRingEquiv, algebraMap R₂ K',
    ⟨⟨inferInstance, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, hinj, RingHom.finite_algebraMap.2 hfin⟩,
    Subtype.val_injective, fun r => rfl, fun y => ?_⟩
  exact (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).commutes y

theorem exists_trait (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (φ : R →+* W)
    (hφ : IsLocalHom φ) (ρ : R →+* R₂) (hρ : ρ.Finite) (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω)
    (m : R₂ →+* Ω) (hm : Function.Injective m) (hc : ∀ r, m (ρ r) = j (algebraMap W _ (φ r))) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧
      ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = m r := by
  first
  | exact @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | (apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension ..)

end GlobalTheory.FieldTraitExt

namespace GlobalTheory.FieldTraitExt

theorem exists_finite_extension_of_trait : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  intro R W _ _ _ _ _ _ hR hW φ _ hφ K' Ω _ _ io j l hio hc
  obtain ⟨R₂, _, _, _, ρ, i, e, hfe, he, heρ, hie⟩ := exists_normalization R hR K' io hio
  obtain ⟨W₂, _, _, _, σ, φ₂, j₂, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, hj₁, hj₂⟩ :=
    exists_trait R R₂ W hW φ hφ ρ hfe.2.2 Ω j (l.comp e) (l.injective.comp he)
      (fun r => by rw [RingHom.comp_apply, heρ, hc])
  refine ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hfe, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, fun r => ?_, hj₁,
    fun r => ?_⟩
  · rw [← heρ, hie]
  · rw [hj₂, RingHom.comp_apply]
    congr 1
    rw [RingEquiv.eq_symm_apply, hie]

end GlobalTheory.FieldTraitExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFieldsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_common_extension_dvr_fraction_fields : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  first | exact @GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | exact GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | (intros; apply GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait <;> assumption)
end
end
