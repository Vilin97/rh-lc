module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory.LieVB GlobalTheory.Conormal

namespace GlobalTheory.SqZeroPt

theorem zeroSec_sqZeroMap (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem Phi_sqZeroMap_comp : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  intro O _ M N _ _ _ _ _ _ _ _ A _ l z h h' w
  have hl := zeroSec_sqZeroMap O M N l
  rw [Phi_apply, Phi_apply, ← cotMap_comp h hl rfl h']
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  have e : (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h ≫ cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) w = (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) ((ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h) ⊤)) w) := rfl
  rw [e, ← hb, cotMap_d (GlobalTheory.GrpTangent.sqZeroMap l) hl _ (le_preimage_top _ ⊤) (le_preimage_top _ ⊤), kappa_d, kappa_d, appLE_top]
  change (toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b)).snd = _
  rw [show toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b) = TrivSqZeroExt.map l (toTsze O M b) from
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)) b)]
  simp

end GlobalTheory.SqZeroPt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentFormOfSqZeroPointLinearNatural

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SqZeroPt

theorem eq_map_of_isSum {O : Type} [CommRing O] {M M' : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup M'] [Module O M'] [Module Oᵐᵒᵖ M']
    [IsCentralScalar O M'] (f : M →ₗ[O] M') (β : TrivSqZeroExt O M →+* TrivSqZeroExt O M')
    (hβ : GlobalTheory.AbTan.IsSum β id f) : β = (TrivSqZeroExt.map f).toRingHom := by
  ext x
  all_goals
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, map_add (f := _), hβ.1, hβ.2]
    simp

theorem Phi_linear_natural : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (v : GlobalTheory.SqZeroPt.TM O M ⟶ A) (h : GlobalTheory.SqZeroPt.zeroSec O M ≫ v = η[A]), (∀ (r : O) w, GlobalTheory.SqZeroPt.Phi v h (r • w) = r • GlobalTheory.SqZeroPt.Phi v h w) ∧ ∀ (M' : Type) [AddCommGroup M'] [Module O M'] [Module Oᵐᵒᵖ M'] [IsCentralScalar O M'] (f : M →ₗ[O] M') (β : TrivSqZeroExt O M →+* TrivSqZeroExt O M'), IsSum β id f → ∀ (v' : GlobalTheory.SqZeroPt.TM O M' ⟶ A) (h' : GlobalTheory.SqZeroPt.zeroSec O M' ≫ v' = η[A]), v'.left = spMap β ≫ v.left → ∀ w, GlobalTheory.SqZeroPt.Phi v' h' w = f (GlobalTheory.SqZeroPt.Phi v h w) := by
  intro O _ A _ M _ _ _ _ v h
  refine ⟨fun r w => Phi_smul O M A v h r w, ?_⟩
  intro M' _ _ _ _ f β hβ v' h' hv w
  have e : v' = GlobalTheory.GrpTangent.sqZeroMap f ≫ v := by
    apply Over.OverMorphism.ext
    rw [hv, eq_map_of_isSum f β hβ]
    rfl
  subst e
  exact Phi_sqZeroMap_comp O M M' A f v h h' w

end GlobalTheory.SqZeroPt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentFormOfSqZeroPointLinearNaturalStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cotangentFormOfSqZeroPoint_linear_natural : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (v : GlobalTheory.SqZeroPt.TM O M ⟶ A) (h : GlobalTheory.SqZeroPt.zeroSec O M ≫ v = η[A]), (∀ (r : O) w, GlobalTheory.SqZeroPt.Phi v h (r • w) = r • GlobalTheory.SqZeroPt.Phi v h w) ∧ ∀ (M' : Type) [AddCommGroup M'] [Module O M'] [Module Oᵐᵒᵖ M'] [IsCentralScalar O M'] (f : M →ₗ[O] M') (β : TrivSqZeroExt O M →+* TrivSqZeroExt O M'), IsSum β id f → ∀ (v' : GlobalTheory.SqZeroPt.TM O M' ⟶ A) (h' : GlobalTheory.SqZeroPt.zeroSec O M' ≫ v' = η[A]), v'.left = spMap β ≫ v.left → ∀ w, GlobalTheory.SqZeroPt.Phi v' h' w = f (GlobalTheory.SqZeroPt.Phi v h w) := by
  first | exact @GlobalTheory.SqZeroPt.Phi_linear_natural | exact GlobalTheory.SqZeroPt.Phi_linear_natural | (intros; apply GlobalTheory.SqZeroPt.Phi_linear_natural <;> assumption)
end
end
