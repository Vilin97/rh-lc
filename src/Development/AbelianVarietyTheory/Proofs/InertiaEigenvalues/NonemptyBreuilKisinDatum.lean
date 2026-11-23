module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEvalTeichmullerTiltStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserEisensteinNotInXPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittResidueFieldInRingOfIntegersStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquiv

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquivStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  first | exact @GlobalTheory.bkStr_quotient_equiv | exact GlobalTheory.bkStr_quotient_equiv | (intros; apply GlobalTheory.bkStr_quotient_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicCompleteStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  first | exact @GlobalTheory.BKReal.eisPoly_distinguished_complete | exact GlobalTheory.BKReal.eisPoly_distinguished_complete | (intros; apply GlobalTheory.BKReal.eisPoly_distinguished_complete <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingOfIntegersFiniteExtIsDVRFiniteUnitIff

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.IntDvr

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧
    Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  intro l _ K
  refine ⟨Formalism.BasicNotions.Examples₂.LB.OL_dvr K, Formalism.BasicNotions.Examples₂.LB.OL_finite K,
    fun x => ⟨fun h => h.map _, fun h => ?_⟩⟩
  rw [Formalism.BasicNotions.Examples₂.LB.isUnit_iff]
  obtain ⟨u, hu⟩ := h
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 (u : OC l).2
  have h2 := (GlobalTheory.RingBasics.mem_OC _).1 ((u⁻¹ : (OC l)ˣ) : OC l).2
  have h3 : ((u : OC l) : ℂ_[l]) * (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l]) = 1 := by
    have := congrArg (fun z : OC l => (z : ℂ_[l])) u.mul_inv
    exact this
  have h4 : ‖((u : OC l) : ℂ_[l])‖ = 1 := by
    have h5 := congrArg norm h3
    rw [norm_mul, norm_one] at h5
    nlinarith [norm_nonneg ((u : OC l) : ℂ_[l]), norm_nonneg (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l])]
  have h6 : ((u : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [hu, coe_intToOC]
  rw [h6, PadicComplex.norm_extends] at h4
  exact h4

end GlobalTheory.IntDvr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingOfIntegersFiniteExtIsDVRFiniteUnitIffStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧ Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  first | exact @GlobalTheory.IntDvr.main | exact GlobalTheory.IntDvr.main | (intros; apply GlobalTheory.IntDvr.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqKerThetaOfDistinguishedAinf

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem span_eq_ker_theta_of_distinguished : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 →
    IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  intro l hl x hx hu
  obtain ⟨ξ, h, -, h1⟩ := GlobalTheory.Prism.exists_generator l
  have h0 : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
  obtain ⟨c, hc⟩ : ξ ∣ x := by
    rw [← Ideal.mem_span_singleton, ← h]; exact hx
  have hφ := (ainfDelta l).φ_eq x
  have hφ' : (ainfDelta l).φ x = WittVector.frobenius x := rfl
  have hfx : WittVector.frobenius x = WittVector.frobenius ξ * WittVector.frobenius c := by
    rw [hc, map_mul]
  rw [hφ', hfx] at hφ
  have h3 := congrArg (Per.θ l) hφ
  rw [map_mul, h1, map_add (f := _), map_pow, map_mul, map_natCast, hx,
    zero_pow hl.out.ne_zero, zero_add] at h3
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h4 : v * WittVector.frobenius c - 1 ∈ Ideal.span {ξ} := by
    rw [← h, RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
    have h5 : Per.θ l (WittVector.frobenius c) = Per.θ l ((ainfDelta l).δ x) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : OC l) ≠ 0) h3
    rw [h5, ← map_mul, hv, map_one]
  have := (GlobalTheory.Per.AinfComplete.main l ξ fun hu =>  (hu.map (Per.θ l)).ne_zero h0).2
  have h5 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h4) 1
  rw [mul_one, sub_add_cancel] at h5
  have h6 : IsUnit c := by
    rw [← (WittVector.frobeniusEquiv l (OCb l)).symm_apply_apply c]
    exact (isUnit_of_mul_isUnit_right h5).map (WittVector.frobeniusEquiv l (OCb l)).symm
  rw [h, hc, Ideal.span_singleton_mul_right_unit h6]

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqKerThetaOfDistinguishedAinfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 → IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  first | exact @GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | exact GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | (intros; apply GlobalTheory.BSP.span_eq_ker_theta_of_distinguished <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wq_map_injective {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] (w : Wq l a →+* O) : Function.Injective w := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h
  · exact (u.isUnit.map w).ne_zero h

theorem nonempty_bk_of_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  intro l hl K
  obtain ⟨hdvr, hfin, hunit⟩ := GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff l K
  obtain ⟨a, ha, w, hK, hw, hres⟩ := GlobalTheory.T.exists_witt_residueField_in_ringOfIntegers l K
  letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c := fun _ => rfl
  haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) :=
    IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm
  haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  obtain ⟨π, Ep, hπ, hE, hne, hmin⟩ :=
    GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow l a ↥(OL K) (wq_map_injective _) hres
  obtain ⟨str, hstr⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv l a ↥(OL K) π Ep hE hmin
  obtain ⟨hδ, hc⟩ := GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete l a Ep hE
  obtain ⟨fl, ev, hfl, hX, hC, hφ⟩ :=
    GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))
  have hpoly : ∀ f : Polynomial (Wq l a),
      Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f) := by
    intro f
    have : ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom =
        (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.C c))
        rw [Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]
      · change Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))
        rw [Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]
    exact congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this
  have hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0 := by rw [hpoly, hmin.1, map_zero]
  refine ⟨{
    a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2
    not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX
    ev_C := hC, ev_frob := hφ
    span_ev := GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf l _ hE0 ?_
    θ_ev := fun r x h => ?_
    gal_w := fun g c => gal_wA l a
      (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (hK hx)) c }⟩
  · rw [← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]
    exact hδ.map ev
  · obtain ⟨f, rfl⟩ := hmin.2.1 r
    rw [hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    rw [← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]

end GlobalTheory.BSP
end
end
