module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
public import ReciprocityTheory.EigenFrames.EigenSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.XiConn
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementC
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
public import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Algebra.Hom.Rat

-- Source module: Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EigenFrameDualOf

section

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.GD (InMul frameM)
open Formalism.L2.Col (Fields Sp)
open Formalism.L2.Ker (Amb DVar)

namespace CapelliMinorMembership

theorem norm_natCast (p : ℕ) [Fact p.Prime] {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have hq : ‖(N : ℚ_[p])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 h)
  have e1 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← hq, ← PadicAlgCl.norm_extends]
    simp
  rw [← e1, ← PadicComplex.norm_extends]
  simp

end CapelliMinorMembership

theorem eigenFrameDual_of (h : ReciprocityTheory.EigenFramesTheory.EigenFrameDual.{0, 0}) : EigenFrameDual := by
  intro E _ _ p _ ι hd τ₀
  exact h p E _ (NumberField.RingOfIntegers.basis E) ι hd τ₀

theorem CapelliMinorMembership.key_term {X : Fields} (A : Amb X) {a b : ℕ} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n₀ : ℕ}
    (hn0 : (n₀ : ℂ_[p]) ≠ 0) (r : X.Tau → Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) → ℂ_[p])
    (τ₁ τ : X.Tau) (β₁ β' β : Fin b) (α₁ α' α : Fin a) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 X.E)) :
    (ι : ℂ →+* ℂ_[p]) (((n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E) β α)
        (τ₁, β₁, α₁)) *
      (if β = β' ∧ α = α' then ι (A.cD τ) * r τ i * (n₀ : ℂ_[p])⁻¹ else 0) =
    if α = α₁ then (if β = β₁ then
      (if β₁ = β' ∧ α₁ = α' then ι (A.cD τ) *
        (r τ i * ι (X.embC A.σ₀ τ₁ ((NumberField.RingOfIntegers.basis X.E i : 𝓞 X.E) : X.E))) else 0)
      else 0) else 0 := by
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hα : α = α₁
  · subst hα
    by_cases hβ : β = β₁
    · subst hβ
      by_cases h' : β = β' ∧ α = α'
      · simp only [vecE, h', and_self, if_true]
        rw [map_mul, map_natCast]
        field_simp
        simp only [RingEquiv.coe_toRingHom]
        ring
      · simp [vecE, h']
    · simp [vecE, hβ, Ne.symm hβ]
  · simp [vecE, hα, Ne.symm hα]

theorem CapelliMinorMembership.collapse {K κ B C : Type} [AddCommMonoid K] [Fintype κ] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (g : κ → K) (β₁ : B) (α₁ : C) :
    ∑ i, ∑ β : B, ∑ α : C, (if α = α₁ then (if β = β₁ then g i else 0) else 0) = ∑ i, g i := by
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem kerFrame_of (h : EigenFrameDual) : KerFrame := by
  intro X A a b N N' L p _ ι hd hinj hcD hn
  obtain ⟨n₀, hn₀, hv⟩ := hn
  choose r hr1 hr2 using fun τ : X.Tau => h X.E p ι hd (X.embC A.σ₀ τ)
  have hn0 : (n₀ : ℂ_[p]) ≠ 0 := by
    intro h0
    have := CapelliMinorMembership.norm_natCast p hn₀
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨Module.Free.ChooseBasisIndex ℤ (𝓞 X.E) × Fin b × Fin a, inferInstance,
    fun j => (n₀ : ℂ) • vecE A.σ₀ ((NumberField.RingOfIntegers.basis X.E j.1 : 𝓞 X.E) : X.E) j.2.1 j.2.2,
    fun j k => if j.2.1 = k.2.1 ∧ j.2.2 = k.2.2 then ι (A.cD k.1) * r k.1 j.1 * (n₀ : ℂ_[p])⁻¹ else 0,
    fun j => hv _ _ _, ?_, ?_⟩
  · intro j k
    dsimp only
    split_ifs
    · rw [norm_mul, norm_mul, norm_inv, CapelliMinorMembership.norm_natCast p hn₀, inv_one, mul_one]
      first
      | exact mul_le_one₀ (hcD _) (norm_nonneg _) (hr1 _ _)
      | nlinarith [norm_nonneg (ι (A.cD k.1)), norm_nonneg (r k.1 j.1), hcD k.1, hr1 k.1 j.1]
    · simp
  · intro i k
    obtain ⟨τ₁, β₁, α₁⟩ := i
    obtain ⟨τ, β', α'⟩ := k
    unfold frameM
    simp only [Fintype.sum_prod_type]
    simp only [CapelliMinorMembership.key_term A ι hn0 r]
    refine (CapelliMinorMembership.collapse _ β₁ α₁).trans ?_
    by_cases hc : β₁ = β' ∧ α₁ = α'
    · refine (Finset.sum_congr rfl (fun i _ => if_pos hc)).trans ?_
      rw [← Finset.mul_sum, hr2 τ (X.embC A.σ₀ τ₁)]
      obtain ⟨rfl, rfl⟩ := hc
      by_cases ht : τ₁ = τ
      · subst ht
        simp
      · have hne : X.embC A.σ₀ τ₁ ≠ X.embC A.σ₀ τ := fun e => ht (hinj e)
        rw [if_neg hne, mul_zero, if_neg]
        intro he
        exact ht (Prod.mk.inj he).1
    · refine (Finset.sum_congr rfl (fun i _ => if_neg hc)).trans ?_
      rw [Finset.sum_const_zero, if_neg]
      intro he
      have h2 := (Prod.mk.inj he).2
      exact hc ⟨(Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

end Formalism.L2.AlgTh
end
end
end

-- Source module: Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

theorem jet_succ_eq {K : Type} [Field K] [CharZero K] (F a : PowerSeries K)
    (h : PowerSeries.derivative (R := K) F = a * F) (i : ℕ) :
    (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, ((i.choose p.1 : ℕ) : K) *
        ((((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a) *
        ((((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F) := by
  have h1 := congrArg (PowerSeries.coeff i) h
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h1
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i,
      ((i.choose p.1 : ℕ) : K) * (((p.1).factorial : ℕ) : K) * (((p.2).factorial : ℕ) : K) =
        ((i.factorial : ℕ) : K) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h2 : p.2 = i - p.1 := by omega
    rw [h2]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : p.1 ≤ i)
  calc (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F
      = ((i.factorial : ℕ) : K) * (PowerSeries.coeff (i + 1) F * ((i : K) + 1)) := by
        rw [Nat.factorial_succ]; push_cast; ring
    _ = ((i.factorial : ℕ) : K) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F := by rw [h1]
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          ((i.factorial : ℕ) : K) * (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F) := by
        rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [← key p hp]
        ring

theorem log_derivative_jets_integral : LogDerJets := by
  intro K _ _ _ F a ρ hρ h hF0 ha i
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
    | succ i =>
      rw [jet_succ_eq F a h i]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hq : p.2 < i + 1 := by omega
      rw [norm_mul, norm_mul]
      have h1 : ‖((i.choose p.1 : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
      have h2 := ha p.1
      have h3 := ih p.2 hq
      calc ‖((i.choose p.1 : ℕ) : K)‖ * ‖(((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a‖ *
            ‖(((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F‖
          ≤ 1 * ρ * ρ ^ p.2 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
              (mul_nonneg zero_le_one hρ0)
        _ = ρ ^ (p.2 + 1) := by ring
        _ ≤ ρ ^ (i + 1) := pow_le_pow_right₀ hρ (by omega)

theorem power_log_derivative_jets : PowLogDer := by
  intro K _ _ G V c M hM hc h
  cases M with
  | zero => omega
  | succ n =>
    have hd := congrArg (PowerSeries.derivative (R := K)) h
    rw [Derivation.leibniz_pow, Derivation.leibniz, PowerSeries.derivative_C] at hd
    simp only [smul_eq_mul, nsmul_eq_mul, smul_zero, add_zero, add_tsub_cancel_right] at hd
    have hC : (PowerSeries.C (c ^ (n + 1)) : PowerSeries K) ≠ 0 := by
      intro h0
      apply pow_ne_zero (n + 1) hc
      simpa using congrArg PowerSeries.constantCoeff h0
    apply mul_left_cancel₀ hC
    rw [map_natCast]
    linear_combination (-((n + 1 : ℕ) : PowerSeries K) * PowerSeries.derivative (R := K) G) * h + G * hd

end Formalism.L2.AlgTh
end
end
end

-- Source module: Formalism.LocalToGlobal.AlgebraicTheory.ColBoundOfPaths

section

@[expose] public section

namespace Formalism.L2.AlgTh

theorem logDerJets : LogDerJets := log_derivative_jets_integral
theorem powLogDer : PowLogDer := power_log_derivative_jets
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
theorem linScale : LinScale := linear_scaling_jets
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
theorem etPower : EtPower := etPower_of unitKerInt
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
theorem tensZEt : TensZEt := tensor_integral_torsion
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
theorem scalarConst : ScalarConst := scalar_constant_value
theorem xiSwap : XiSwap := xi_swap
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
end
end

-- Source module: ReciprocityTheory.EigenFrames.EigenPf

section

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField

namespace ReciprocityTheory.EigenFramesTheory

theorem norm_le_one_of_monic {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ} (hf : f.Monic) {y : ℂ_[p]}
    (h : Polynomial.eval₂ (Int.castRingHom ℂ_[p]) y f = 0) : ‖y‖ ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  set n := f.natDegree
  have hn : n ≠ 0 := by
    intro h0
    have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf h0
    rw [hf1, Polynomial.eval₂_one] at h
    exact one_ne_zero h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at h
  set S := ∑ i ∈ Finset.range n, Int.castRingHom ℂ_[p] (f.coeff i) * y ^ i
  have hS : ‖S‖ ≤ ‖y‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    refine (mul_le_of_le_one_left (by positivity) ?_).trans (pow_le_pow_right₀ hy.le hi')
    rw [eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  have hyn : y ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hS
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ hy (by omega)
  linarith

theorem eig_norm_det_le_one {p : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ_[p]) (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hM _ _)

theorem eig_norm_intCast {p : ℕ} [Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℂ_[p])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

universe u v

theorem eigenFrameDual : EigenFrameDual.{u, v} := by
  intro p _ E _ _ κ _ b ι hd τ₀
  classical
  let bQ : Module.Basis κ ℚ E := b.localizationLocalization ℚ (nonZeroDivisors ℤ) E
  have hbQ : ∀ i, bQ i = ((b i : 𝓞 E) : E) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) E b i
  have hcard : Fintype.card κ = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis bQ]
  let e : κ ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let N : Matrix κ κ ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ bQ e
  have hN : N.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ) := by
    rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ e,
      Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E b, NumberField.discr_eq_discr E b]
    simp
  let M : Matrix κ κ ℂ_[p] := (ι : ℂ →+* ℂ_[p]).mapMatrix N
  have hMa : ∀ i j, M i j = ι (e j ((b i : 𝓞 E) : E)) := by
    intro i j
    rw [← hbQ]
    rfl
  have hM2 : M.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ_[p]) := by
    rw [← RingHom.map_det, ← map_pow, hN, map_intCast]
  have hM1 : ‖M.det‖ = 1 := by
    have h := congrArg norm hM2
    rw [norm_pow, eig_norm_intCast hd] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hM0 : M.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hM1
    exact zero_ne_one hM1
  have hint : ∀ i j, ‖M i j‖ ≤ 1 := by
    intro i j
    obtain ⟨f, hmon, hf⟩ := (NumberField.RingOfIntegers.isIntegral_coe (b i) : IsIntegral ℤ ((b i : 𝓞 E) : E))
    refine norm_le_one_of_monic hmon ?_
    let g : E →+* ℂ_[p] := (ι : ℂ →+* ℂ_[p]).comp (e j : E →+* ℂ)
    have h := congrArg g hf
    rw [map_zero, Polynomial.hom_eval₂] at h
    rw [RingHom.ext_int (g.comp (algebraMap ℤ E)) (Int.castRingHom ℂ_[p])] at h
    rw [hMa]
    exact h
  let j₀ : κ := e.symm τ₀.toRatAlgHom
  refine ⟨fun i => (M.det)⁻¹ * M.adjugate j₀ i, fun i => ?_, fun φ => ?_⟩
  · rw [norm_mul, norm_inv, hM1, inv_one, one_mul, Matrix.adjugate_apply]
    refine eig_norm_det_le_one _ fun a c => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hint a c
  · let j : κ := e.symm φ.toRatAlgHom
    have hφ : ∀ i, ι (φ ((b i : 𝓞 E) : E)) = M i j := by
      intro i
      rw [hMa, Equiv.apply_symm_apply]
      rfl
    have h1 : ∑ i, M.adjugate j₀ i * M i j = M.det * (if j₀ = j then 1 else 0) := by
      have h := congrFun (congrFun (Matrix.adjugate_mul M) j₀) j
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
      exact h
    simp only [hφ, mul_assoc]
    rw [← Finset.mul_sum, h1, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    by_cases hc : φ = τ₀
    · subst hc
      simp [j, j₀]
    · rw [if_neg hc, if_neg]
      intro hj
      apply hc
      have h2 : τ₀.toRatAlgHom = φ.toRatAlgHom := e.symm.injective hj
      ext x
      exact (DFunLike.congr_fun h2 x).symm

end ReciprocityTheory.EigenFramesTheory
end
end
end

-- Source module: Formalism.LocalToGlobal.AlgebraicTheory.SplitPlaceScaledBound

section

@[expose] public section

namespace Formalism.L2.AlgTh

theorem xiConn : XiConn := xiConn_of etLoc scalarConst xiSwap
theorem split_place_scaled_bound : SelfDualLatticeThetaPadicIntegrality := split_bound_of_xi_lemmas xiEt xiConn
theorem eigenFrameDual : EigenFrameDual := eigenFrameDual_of ReciprocityTheory.EigenFramesTheory.eigenFrameDual
theorem kerFrame : KerFrame := kerFrame_of eigenFrameDual

end Formalism.L2.AlgTh
end
end
