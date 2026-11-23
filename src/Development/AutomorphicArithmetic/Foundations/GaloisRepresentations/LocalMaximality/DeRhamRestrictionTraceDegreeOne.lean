module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChart

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.ResEv

open MvPolynomial

theorem ker_aeval_zero (k : Type) [Field k] (d : ℕ) :
    RingHom.ker (aeval (R := k) (fun _ : Fin d ↦ (0 : k))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p = AddMonoidAlgebra.coeff p 0 := by
      rw [show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp

theorem res_aeval (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F)
    (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes k x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d ↦ x j.succ / x 0) p) = aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [hρ.1]
    · obtain ⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by
        by_contra h; push_neg at h; exact hn (Finsupp.ext h)
      have h0 : ∏ j : Fin d, (0 : k) ^ n j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)
      rw [h0, smul_zero]
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))
      have hsum : ∑ i, m i = 0 := by
        rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        have := congrFun h j0.succ
        simp [m] at this
        exact hj0 this
      have hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]
        rw [Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib,
          Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]
      rw [hprod, hρ.2 m hsum hm, mul_zero]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]

end GlobalTheory.PD.ResEv

open MvPolynomial in
theorem GlobalTheory.PD.ResEv.chart0 : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  intro k _ F _ _ d x hx ρ hρ
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0
  have hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p := by
    intro p
    have h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [he]
    exact congrArg (fun f => f p) (congrArg DFunLike.coe h1)
  refine ⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩
  · have := GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)
    rw [← hv, AlgEquiv.apply_symm_apply] at this
    simpa using this
  · have ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X := by
      rw [← Set.range_comp]
      congr 1
      funext j
      apply Subtype.ext
      simp [he]
    rw [ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]
    ext a
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChartStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  first | (exact @GlobalTheory.PD.ResEv.chart0) | (exact GlobalTheory.PD.ResEv.chart0) | (intros; apply GlobalTheory.PD.ResEv.chart0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePoints

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.FibTrace

theorem trace_quot_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc hk hred h
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJ
  haveI : Module.Finite k (rB k K x {0} ⧸ J) := GlobalTheory.PD.FibFin.finite_quot k K x hc
  haveI : Module.Free k (rB k K x {0} ⧸ J) := Module.Free.of_divisionRing k _
  have hred' : IsReduced (k ⊗[k] (rB k K x {0} ⧸ J)) :=
    isReduced_of_injective (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).toRingHom
      (Algebra.TensorProduct.lid k (rB k K x {0} ⧸ J)).injective
  have key := (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange (O := k) (H := rB k K x {0} ⧸ J) (K := k) hred').2.2
    (Ideal.Quotient.mk J h)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at key
  rw [key]
  have hker : ∀ e : fib k K x, ∀ a ∈ J, e.1 a = 0 := fun e a ha => by
    have : J ≤ RingHom.ker e.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact e.2 j
    exact this ha
  let E : fib k K x ≃ (rB k K x {0} ⧸ J →ₐ[k] k) :=
    { toFun := fun e => Ideal.Quotient.liftₐ J e.1 (hker e)
      invFun := fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ k J), fun j => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        have hm : (⟨_, tco_mem k K x j⟩ : rB k K x {0}) ∈ J := by
          rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]⟩
      left_inv := fun e => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun φ => by
        apply Ideal.Quotient.algHom_ext
        rfl }
  rw [← finsum_comp_equiv E]
  rfl

end GlobalTheory.PD.FibTrace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePointsStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (exact GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (intros; apply GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibre

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem trF_locCoch_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h
  have hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x := if_pos rfl
  have h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [h1]
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1
  haveI := hc.fin
  have hint : IsIntegral (rA k x {0}) (h : K) := h.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)
  obtain ⟨ev, hev, hker⟩ := GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ
  have ha' : (a : F) = Algebra.trace F K (h : K) := ha
  rw [← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]

end GlobalTheory.PD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (exact GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (intros; apply GlobalTheory.PD.trF_locCoch_eq_finsum_fib  <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRestrictionTraceDegreeOne

section

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one :
    ResidueOfTraceIsFiberSum := by
  intro F L _ _ _ _ _ _ d x hc hred ρ hρ h
  obtain ⟨⟨τ, hτ⟩, -⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F L d (xv x) hc
  have hloc : locCoch ℂ L (xv x) (h : L) Finset.univ = (h : L) • vol0 ℂ L (xv x) := if_pos rfl
  have h1 : trF ℂ τ ρ (locCoch ℂ L (xv x) (h : L) Finset.univ) = ρ (Algebra.trace F L (h : L)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← h1]
  exact GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre ℂ F L d (xv x) hc τ hτ ρ hρ inferInstance hred h
end
end
