module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankarStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAtPrimeEtaleCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNormalCoords
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanX

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC

theorem ker_reduceLoc_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  intro T O _ _ _ _ _ _ A A₁ _ _ f i i₁ EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit hker
  have hψ : ∀ p : A₁[X], algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) p =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) p) :=
    fun _ => rfl
  have hC : ∀ c : A₁, algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) c =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) (C c)) := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), IsScalarTower.algebraMap_apply A₁ A₁[X] (Ext f EA)]
    rfl
  have hlocX : locBC f i i₁ EA QA jA hcomp hj (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA), locBC_algebraMap]
    have h1 : inclE f EA (algebraMap A[X] EA Polynomial.X) =
        algebraMap A[X] (Ext f EA) Polynomial.X :=
      (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
    rw [h1, Algebra.TensorProduct.algebraMap_apply, algebraMap_polyOver, Polynomial.map_X]
    rfl
  have hpol : ∀ q : A₁[X],
      Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X})
        (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) q)) =
      Ideal.Quotient.mk _ (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (Polynomial.eval 0 q)) := by
    intro q
    rw [hC, Ideal.Quotient.eq, ← map_sub, ← map_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [hr, map_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : (Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X}) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* _) =
      (Ideal.Quotient.mk _).comp ((algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x =>
      rw [reduce_tmul]
      dsimp only
      have hsplit : (p ⊗ₜ[A[X]] x : Ext f EA) =
          algebraMap A₁[X] (Ext f EA) p * inclE f EA x := by
        show (p ⊗ₜ[A[X]] x : Ext f EA) = (p ⊗ₜ[A[X]] (1 : EA)) * ((1 : PolyOver f) ⊗ₜ[A[X]] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      simp only [map_mul]
      congr 1
      · exact hpol p
      · rw [← locBC_algebraMap, ← locBC_algebraMap_base]
        have hmem : algebraMap EA (Localization.AtPrime QA) x -
            algebraMap A (Localization.AtPrime QA) (ρ (algebraMap EA (Localization.AtPrime QA) x)) ∈
              RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub]
          have := congrArg (fun w => w (ρ (algebraMap EA (Localization.AtPrime QA) x))) hρA
          simp only [RingHom.comp_apply, RingHom.id_apply] at this
          rw [this, sub_self]
        rw [hker, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, hlocX]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h := congrArg (fun w => w x) key
    simp only [RingHom.comp_apply, hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X) = 0
    rw [hψ, reduceLoc, IsLocalization.lift_eq,
      show algebraMap A₁[X] (Ext f EA) Polynomial.X = (@id (PolyOver f) Polynomial.X) ⊗ₜ[A[X]] (1 : EA)
        from rfl, reduce_tmul]
    show Polynomial.eval 0 (Polynomial.X : A₁[X]) * _ = 0
    rw [Polynomial.eval_X, zero_mul]

end GlobalTheory.KeyOriginBC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanXStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.ker_baseChangedReduction_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  first | (exact @GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (exact GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (intros; apply GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalLocalRingEtaleBaseChange

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.normal_local_ring_etale_base_change : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (exact GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange) | (intros; apply GlobalTheory.KeyOriginBCEt.closureEtaleAt_baseChange  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOne

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC



theorem etale_bc : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA
    hFits ρ hρ hpt a ha0 ha A₁ _ _ _ _ _ _ f i₁ hf hi₁ hloc₁ hcomp hK
  obtain ⟨-, -, hqA, -, hj, hψ, htor⟩ := hFits
  obtain ⟨hρA, hρker, hρmod⟩ := hρ
  have hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0 := by
    rw [← RingHom.mem_ker, hρker]; exact Ideal.subset_span rfl
  have hmax := comap_maximalIdeal_eq_origin P φ hφ hsh hP
  set β := fibBC f i i₁ EA QA jA hcomp hj hf with hβ
  have hcong := reduce_sub_glue_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hρmod
  have hunit := isUnit_reduce f i i₁ EA QA jA hcomp hj ρ hρA hρX hmax hloc₁ hcong
  refine ⟨Ext f EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ideal₁ f i i₁ EA QA jA hcomp hj, inferInstance, locMap f i i₁ EA QA jA hcomp hj,
    fibMap f i i₁ EA QA jA hcomp hj hi₁, BC β DA, inferInstance, inferInstance, bcAct β DA q actA,
    ⟨hi₁, hloc₁, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, β, inclD β DA, ?_,
    inclD_algebraMap β DA⟩
  · simpa using hqA.map f
  · exact comap_ideal₁_eq_origin f i i₁ EA QA jA hcomp hj hmax hloc₁
  · apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj),
      locMap_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [glue_tmul]
    change algebraMap T[X] O (Polynomial.map i₁ p) * _ = _
    simp
  · exact IsLocalization.lift_comp _
  · exact isZTorsor_bc β DA q hq actA htor
  · apply RingHom.ext; intro x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    simp only [reduceLoc, IsLocalization.lift_eq, algebraMap_ext, reduce_tmul]
    change Polynomial.eval 0 (Polynomial.C x) * _ = _
    simp
  · exact GlobalTheory.T.ker_baseChangedReduction_eq_span_X T O A A₁ f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hρker
  · exact reduceLoc_sub_locMap_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hcong
  · exact GlobalTheory.T.localization_at_prime_etale_compat T O A A₁ f i i₁ hf EA QA jA hcomp hj ρ hρA hρX hunit DA q actA hq htor hpt
  · intro P₁ _ hP₁
    by_cases h : algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁
    · exact GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 hK P₁ hP₁ h
    · exact GlobalTheory.T.normal_local_ring_etale_base_change T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 ha P₁ h
  · have hloc : (locMap f i i₁ EA QA jA hcomp hj).comp (locBC f i i₁ EA QA jA hcomp hj) = jA := by
      apply IsLocalization.ringHom_ext QA.primeCompl
      apply RingHom.ext; intro x
      simp [locBC_algebraMap, locMap_algebraMap, glue_inclE]
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hβ, fibBC_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply ψA, hψ]
    simp only [fibMap, IsLocalization.lift_eq, RingHom.comp_apply]
    rw [← RingHom.comp_apply (locMap f i i₁ EA QA jA hcomp hj), hloc]

end GlobalTheory.KeyOriginBC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOneStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.baseChange_integralClosure_etale_height_one : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  first | (exact @GlobalTheory.KeyOriginBC.etale_bc) | (exact GlobalTheory.KeyOriginBC.etale_bc) | (intros; apply GlobalTheory.KeyOriginBC.etale_bc  <;> assumption)
end
end
