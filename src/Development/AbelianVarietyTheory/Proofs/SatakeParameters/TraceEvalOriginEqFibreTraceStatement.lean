module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
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
public import Mathlib.RingTheory.Trace.Quotient
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceQuotientEqOfProjective

section

@[expose] public section

namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x]
  simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTrace

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.TraceOrigin


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ev_eq_trace_quot : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  intro k _ _ F K _ _ _ _ _ _ d x hc ev hker h a ha
  haveI : Module.IsTorsionFree (rA k x {0}) (integralClosure (rA k x {0}) K) := inferInstance
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {0}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI := hc.fin
  haveI : Module.Finite (rA k x {0}) (integralClosure (rA k x {0}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {0} (Finset.singleton_nonempty 0)).1
  haveI := GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hc 0
  haveI : IsIntegrallyClosed (integralClosure (rA k x {0}) K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  have hsurj : Function.Surjective ev := fun c => ⟨algebraMap k _ c, ev.commutes c⟩
  haveI hmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let h' : integralClosure (rA k x {0}) K := ⟨h.1, h.2⟩
  have hint : a = Algebra.intTrace (rA k x {0}) (integralClosure (rA k x {0}) K) h' := by
    apply Subtype.ext
    exact ha.trans (Algebra.algebraMap_intTrace (A := rA k x {0}) (K := F) (L := K) h').symm
  have key := GlobalTheory.trace_quotient_eq_of_projective (rA k x {0}) (integralClosure (rA k x {0}) K) (RingHom.ker ev) h'
  set p := RingHom.ker ev with hp
  let e₁ : (rA k x {0}) ⧸ p ≃+* k := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
  have he₁ : ∀ y, e₁ (Ideal.Quotient.mk p y) = ev y := fun y => rfl
  let φ : integralClosure (rA k x {0}) K ≃+* rB k K x {0} :=
    { toFun := fun b => ⟨b.1, b.2⟩, invFun := fun b => ⟨b.1, b.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJdef
  have hJ : J = (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))).map φ := by
    rw [hker, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  let e₂ := Ideal.quotientEquiv (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))) J φ hJ
  have hcomm : (algebraMap k (rB k K x {0} ⧸ J)).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap _ _) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
    change Ideal.Quotient.mk J (algebraMap k _ (ev y)) = Ideal.Quotient.mk J (φ (algebraMap _ _ y))
    rw [Ideal.Quotient.eq]
    have hmem : y - algebraMap k _ (ev y) ∈ p := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h3 : φ (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K) (y - algebraMap k _ (ev y))) ∈ J :=
      hJ ▸ Ideal.mem_map_of_mem φ (Ideal.mem_map_of_mem _ hmem)
    convert J.neg_mem h3 using 1
    rw [map_sub, map_sub, neg_sub]
    congr 1
    apply Subtype.ext
    change algebraMap k K (ev y) = algebraMap F K (algebraMap k F (ev y))
    exact IsScalarTower.algebraMap_apply k F K _
  have htr := Algebra.trace_eq_of_equiv_equiv e₁ e₂ hcomm (Ideal.Quotient.mk _ h')
  rw [key] at htr
  have h2 : e₂ (Ideal.Quotient.mk _ h') = Ideal.Quotient.mk J h := rfl
  have := congrArg e₁ htr
  rw [RingEquiv.apply_symm_apply, h2, he₁] at this
  rw [hint, this]

end GlobalTheory.PD.TraceOrigin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_eval_origin_eq_fibre_trace : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  first | (exact @GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (exact GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (intros; apply GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot  <;> assumption)
end
end
