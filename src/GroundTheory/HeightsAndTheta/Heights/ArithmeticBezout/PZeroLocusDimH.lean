module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHGeo
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeOfAddOneLeSucc
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHAlg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem ringKrullDim_le_of_isIntegral_inj {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem aeval_derivative_minpoly_ne_zero {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hx : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  intro h0
  have hdvd := minpoly.isIntegrallyClosed_dvd hx h0
  have hmon := minpoly.monic hx
  have hne : Polynomial.derivative (minpoly R x) ≠ 0 := by
    intro hd
    exact (minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)
  have h1 := Polynomial.degree_le_of_dvd hdvd hne
  have h2 := Polynomial.degree_derivative_lt hmon.ne_zero
  exact absurd h1 (not_le.2 h2)

theorem exists_simple_root_data {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)
  let _ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := ⟨hint⟩
  have hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩
  choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))
  have hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom =
      algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      change _ = g (C a)
      rw [← MvPolynomial.algebraMap_eq, g.commutes]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hπ j
  have hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n),
      Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
        Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q := by
    intro Q i
    rw [Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]
  have hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  refine ⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_,
    fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey]
    exact aeval_derivative_minpoly_ne_zero hinj _

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem eval_eval₂_aeval {n s : ℕ} (π : Fin s → MvPolynomial (Fin n) ℂ)
    (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (x : Fin n → ℂ) (i : Fin n) :
    MvPolynomial.eval x (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
      Polynomial.eval (x i) (Q.map (MvPolynomial.eval (paramMap π x))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval_map, MvPolynomial.eval_X]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · simp
  · simp [paramMap]

theorem mem_zeroSet_iff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    (∀ q ∈ I, MvPolynomial.eval x q = 0) ↔ I ≤ RingHom.ker (MvPolynomial.eval x) :=
  ⟨fun h q hq => RingHom.mem_ker.2 (h q hq), fun h _ hq => RingHom.mem_ker.1 (h hq)⟩

theorem ringKrullDim_quot_sup_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

theorem le_of_add_one_le_succ {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (k : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ h

theorem dimH_le_of_step {n : ℕ} (d : ℕ)
    (hIH : ∀ J' : Ideal (MvPolynomial (Fin n) ℂ), ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal))
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d) :
    dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by

  have hcover : {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ⊆
      ⋃ p ∈ J.minimalPrimes, {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, mem_zeroSet_iff] at hx
    have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hx
    exact Set.mem_biUnion hp ((mem_zeroSet_iff p x).2 hpx)
  refine (dimH_mono hcover).trans ?_
  rw [dimH_bUnion (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).countable]
  refine iSup₂_le fun p hp => ?_
  have : p.IsPrime := hp.1.1
  have hpd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)).trans hJ
  obtain ⟨s, hs, π, P, hP, hP'⟩ := exists_simple_root_data p
  set g := ∏ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) with hgdef
  have hg : g ∉ p := by
    rw [hgdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hP' i hi
  have hsplit : {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ⊆
      {x | x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ∧ ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ∪
      {x : Fin n → ℂ | ∀ q ∈ p ⊔ Ideal.span {g}, MvPolynomial.eval x q = 0} := by
    intro x hx
    by_cases h : ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0
    · exact Or.inl ⟨hx, h⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_ofPred_eq, mem_zeroSet_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem,
        RingHom.mem_ker]
      refine ⟨(mem_zeroSet_iff p x).1 hx, ?_⟩
      rw [hgdef, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_eval₂_aeval]; exact hi)
  refine (dimH_mono hsplit).trans ?_
  rw [dimH_union]
  refine max_le ?_ ?_
  · have hV : ∀ x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}, ∀ i,
        Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0 := by
      intro x hx i
      rw [← eval_eval₂_aeval]
      exact hx _ (hP i)
    refine (dimH_simple_roots_le π P _ hV).trans ?_
    have hsd : s ≤ d := by exact_mod_cast hs.trans hpd
    have : (s : ENNReal) ≤ d := by exact_mod_cast hsd
    gcongr
  · exact hIH _ ((ringKrullDim_quot_sup_add_one_le p g hg).trans hpd)

theorem dimH_zeroLocus_le (d : ℕ) : ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by
  induction d with
  | zero =>
    intro n J hJ
    refine dimH_le_of_step 0 (fun J' hJ' => ?_) J hJ
    by_cases htop : J' = ⊤
    · have : {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
      rw [this, dimH_empty]
      simp
    · have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J') := Ideal.Quotient.nontrivial_iff.2 htop
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J')
      have h1 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 := by gcongr
      have h2 := h1.trans hJ'
      rw [zero_add, Nat.cast_zero] at h2
      exact absurd h2 (not_le.2 zero_lt_one)
  | succ k ih =>
    intro n J hJ
    refine dimH_le_of_step (k + 1) (fun J' hJ' => ?_) J hJ
    refine (ih n J' (le_of_add_one_le_succ hJ')).trans ?_
    have : (k : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.le_succ k
    gcongr

theorem proof : Statement := fun n d J hJ => dimH_zeroLocus_le d n J hJ

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end
end
