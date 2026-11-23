module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmeticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafPullbackEqDivisorOfApproxStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentreStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitOfPoint

variable {p : ℕ} [Fact p.Prime]

theorem base_integralClosure (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ _ : IsDiscreteValuationRing (integralClosure ℤ_[p] K), GlobalTheory.Mum.Base (integralClosure ℤ_[p] K) := by
  haveI := GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  exact ⟨inferInstance, ⟨inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure K⟩, GlobalTheory.charZero_integralClosure_padicInt⟩

theorem lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have hft := h.ft
  have := M.lft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

end GlobalTheory.Poinc.TraitOfPoint


open GlobalTheory.Poinc.TraitOfPoint Polynomial in
theorem GlobalTheory.Poinc.exists_trait_of_classical_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  intro g n F Z i hi W8 X₁ Y πY p _ y hy
  haveI := hi
  haveI := lft_toInt Y
  obtain ⟨K, hK, H⟩ := GlobalTheory.padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := H K le_rfl
  obtain ⟨hdvr, hbase⟩ := base_integralClosure K

  have hinj₀ : Function.Injective (algebraMap (integralClosure ℤ_[p] K) (PadicAlgCl p)) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  let ι₀ : FractionRing (integralClosure ℤ_[p] K) →+* PadicAlgCl p := IsFractionRing.lift hinj₀
  have hgen : gPt p ≫ spMap j₀ = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) :=
    GlobalTheory.ArcPointDescent.sp_sq fun a => by
      simp only [ι₀, IsFractionRing.lift_algebraMap]
      exact hj₀ a
  have hrange : Set.range (jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hw : w = spMap ι₀ (IsLocalRing.closedPoint (PadicAlgCl p)) := Subsingleton.elim _ _
    refine hy ⟨IsLocalRing.closedPoint (PadicAlgCl p), ?_⟩
    have e : gPt p ≫ y ≫ πY ≫ X₁.π = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := by
      rw [← hy₀]
      simp only [← Category.assoc]
      rw [hgen]
    rw [e, hw]
    exact Scheme.Hom.comp_apply _ _ _
  let yK := IsOpenImmersion.lift i _ hrange
  obtain ⟨T, f, fK, hfinj, -, hffin, hfK, hTy⟩ :=
    GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F (integralClosure ℤ_[p] K) hbase hdvr yK

  letI : Algebra (integralClosure ℤ_[p] K) T.V := f.toAlgebra
  haveI : Module.Finite (integralClosure ℤ_[p] K) T.V := hffin
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) T.V :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (FractionRing T.V) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    rw [IsScalarTower.algebraMap_eq (integralClosure ℤ_[p] K) T.V (FractionRing T.V)]
    exact (IsFractionRing.injective T.V (FractionRing T.V)).comp hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (PadicAlgCl p) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj₀
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) T.V := inferInstance
  haveI : Algebra.IsAlgebraic T.V (FractionRing T.V) := IsLocalization.isAlgebraic _ (nonZeroDivisors T.V)
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) (FractionRing T.V) :=
    Algebra.IsAlgebraic.trans (integralClosure ℤ_[p] K) T.V (FractionRing T.V)
  let ι' : FractionRing T.V →ₐ[integralClosure ℤ_[p] K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι : FractionRing T.V →+* PadicAlgCl p := ι'.toRingHom
  have hιf : ∀ a : integralClosure ℤ_[p] K, ι (algebraMap T.V (FractionRing T.V) (f a)) = ((a : K) : PadicAlgCl p) := by
    intro a
    have h1 := ι'.commutes a
    rw [IsScalarTower.algebraMap_apply (integralClosure ℤ_[p] K) T.V (FractionRing T.V)] at h1
    exact h1

  let φ : ℤ_[p] →+* T.V := f.comp (algebraMap ℤ_[p] (integralClosure ℤ_[p] K))
  have hcomp : ι.comp ((algebraMap T.V (FractionRing T.V)).comp φ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
    ext c
    change ι (algebraMap T.V (FractionRing T.V) (f (algebraMap ℤ_[p] (integralClosure ℤ_[p] K) c))) = _
    rw [hιf]
    rfl
  have hφint : φ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x) hffin.to_isIntegral

  have hint : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, hPm, hP⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (ι x)).2 hx
      have hTV : IsIntegral T.V x := by
        refine ⟨P.map φ, hPm.map φ, ?_⟩
        rw [Polynomial.eval₂_map]
        apply ι.injective
        rw [Polynomial.hom_eval₂, hcomp, map_zero]
        exact hP
      exact IsIntegrallyClosed.isIntegral_iff.1 hTV
    · rintro ⟨v, rfl⟩
      obtain ⟨P, hPm, hP⟩ := hφint v
      apply (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
      refine ⟨P, hPm, ?_⟩
      have h2 := congrArg (ι.comp (algebraMap T.V (FractionRing T.V))) hP
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [← hcomp, ← RingHom.comp_assoc]
      exact h2
  let j : T.V →+* OO p := (ι.comp (algebraMap T.V (FractionRing T.V))).codRestrict (OO p) fun v =>
    (mem_OO_iff _).2 ((hint _).2 ⟨v, rfl⟩)
  have hjf : j.comp f = j₀ := by
    ext a
    change ι (algebraMap T.V (FractionRing T.V) (f a)) = ((j₀ a : OO p) : PadicAlgCl p)
    rw [hιf, hj₀]
  refine ⟨T, ι, j, spMap f ≫ y₀, hint, fun v => rfl, ?_, ?_, ?_⟩
  · refine ⟨fun v hv => ?_⟩
    have h1 : ‖ι (algebraMap T.V (FractionRing T.V) v)‖ = 1 :=
      le_antisymm ((hint _).2 ⟨v, rfl⟩) (not_lt.1 fun h => ((not_isUnit_OO_iff (j v)).2 h) hv)
    have h0 : algebraMap T.V (FractionRing T.V) v ≠ 0 := fun h => by
      rw [h, map_zero, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨w, hw⟩ := (hint (algebraMap T.V (FractionRing T.V) v)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective T.V (FractionRing T.V) ?_)
    rw [map_mul, map_one, hw, mul_inv_cancel₀ h0]
  · rw [← Category.assoc, GlobalTheory.ArcPointDescent.sp_comp (h := j₀) (fun a => by rw [← hjf]; rfl), hy₀]
  · have e1 : jK T.V ≫ spMap f = spMap fK ≫ jK (integralClosure ℤ_[p] K) :=
      GlobalTheory.ArcPointDescent.sp_sq fun a => (hfK a).symm
    have hyK : yK ≫ i = jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
    rw [hTy, Category.assoc (spMap fK) yK i, hyK]
    simp only [← Category.assoc]
    rw [e1]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  first | exact @GlobalTheory.Poinc.exists_trait_of_classical_point | exact GlobalTheory.Poinc.exists_trait_of_classical_point | (intros; apply GlobalTheory.Poinc.exists_trait_of_classical_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultiple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem approxAt_mul_of_one_le (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ) (hm : 1 ≤ m) (hd : ApproxAt X₁ φ d) :
    ApproxAt X₁ φ (d * m) := by
  intro p _ z₁ c₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ c₀ e
  have hpow : ∀ c : CTrait X₁ p z₁, ‖c.val (f ^ m)‖ = ‖c.val f‖ ^ m := fun c => by
    rw [CTrait.val_eq_valInt, CTrait.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ c : CTrait X₁ p z₁, Real.exp (-(c.sc * (((d * m : ℕ) : ℝ) * φ.evalZ c.T.β))) =
      Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ^ m := fun c => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun c => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf c with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (c.norm_val_le f) (by omega)).trans h2

theorem approxAt_mul : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := approxAt_mul_of_one_le

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultipleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.hasApproxPoincareSeries_nat_multiple : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := by
  first | exact @GlobalTheory.Poinc.approxAt_mul | exact GlobalTheory.Poinc.approxAt_mul | (intros; apply GlobalTheory.Poinc.approxAt_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.DescentPow

theorem exists_cTrait_norm_eqAt {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z} (hi : IsOpenImmersion i)
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun ℤ) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a})
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ c : CTrait X₁ p z₁, c.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(c.sc * (ι * φ.evalZ c.T.β))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait g n F Z i hi W8 X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨a, ha, hI⟩ := hord T ξ hT
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.β)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W8 hE hθi X₁ ι Y πY D hι hP hHom hprop hnorm hsupp hord
  have hi : IsOpenImmersion i := hθ.2.2.1
  obtain ⟨d, hd, hA⟩ := GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points g n F W8 Z i X₁ hE hθi hg φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : ApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ GlobalTheory.T.hasApproxPoincareSeries_nat_multiple g n F W8 Z i X₁ φ d m hm0 hA

  have hord' : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = (Nat.lcm ι d : ℕ) * φ.evalZ T.β ∧ idlAlong (D.nsmul k).idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
    intro T ξ h
    obtain ⟨a, ha, hI⟩ := hord T ξ h
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ i.opensRange
  have hmemU : ∀ y : Y.Z, y ∈ U ↔ X₁.π (πY y) ∈ Set.range i := fun y => by
    show (πY ≫ X₁.π) y ∈ Set.range i ↔ _
    rw [Scheme.Hom.comp_apply]
  have hU : (U : Set Y.Z).Nonempty := by
    refine ⟨Y.pt (closedPoint X₁.Ω₁), (hmemU _).2 ?_⟩
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u ≫ i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact ⟨_, e'.symm⟩
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hsupp x (hsub x hx) ((hmemU x).1 hxU)
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro q _ y hy _ ⟨w, rfl⟩
    have := (hmemU _).1 (hy ⟨w, rfl⟩)
    simpa only [← Category.assoc, Scheme.Hom.comp_apply] using this
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨c, hcy, hc⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, c.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ c.y) _ = _
        rw [hcy]
      rcases hfall c with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, hc f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.Poinc.DescentPow
end
end
end
