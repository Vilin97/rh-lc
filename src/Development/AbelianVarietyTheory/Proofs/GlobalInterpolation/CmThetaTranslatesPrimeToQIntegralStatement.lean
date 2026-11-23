module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnitStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrime
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaIteratedDerivZeroAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrimeStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  first | exact @GlobalTheory.MomN.latInt_th0_of_split_prime | exact GlobalTheory.MomN.latInt_th0_of_split_prime | (intros; apply GlobalTheory.MomN.latInt_th0_of_split_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegrality

section

@[expose] public section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

noncomputable section
namespace GlobalTheory.MomTrans

variable {g : ℕ}

theorem ok_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : z ∈ OK d) : (n : ℂ) * z ∈ OK d := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem nnBasis_of_frame (q : ℕ) (S : Setup g) (hO : S.Ok) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i, x i ∈ S.La) (hb : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) : S.NNBasis q x := by
  classical
  have key : ∀ (c : Fin g → ℂ) (j : Fin g), beta S.d S.Hm (∑ i, c i • x i) (x j) = c j * a j := by
    intro c j
    rw [GlobalTheory.MomOne.Translates.beta_sum_left]
    simp [hb]
  have hli : LinearIndependent ℂ x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := key c j
    rw [hc] at h
    have h0 : beta S.d S.Hm 0 (x j) = 0 := by simp [beta, hf]
    rw [h0] at h
    have : (a j : ℂ) ≠ 0 := by exact_mod_cast (ha j).1.ne'
    exact (mul_eq_zero.1 h.symm).resolve_right this
  let B := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge
  have hB : ∀ i, B i = x i := fun i => by simp [B]
  refine ⟨hx, fun y hy => ?_, fun c _ hc i => ?_⟩
  · have hy' : y = ∑ i, B.repr y i • x i := by
      conv_lhs => rw [← B.sum_repr y]
      simp only [hB]
    have hr : ∀ i, beta S.d S.Hm y (x i) = B.repr y i * a i := by
      intro i; conv_lhs => rw [hy']
      exact key _ i
    refine ⟨∏ i, a i, Nat.Coprime.prod_left fun i _ => (ha i).2,
      fun i => ((∏ j ∈ Finset.univ.erase i, a j : ℕ) : ℂ) * beta S.d S.Hm y (x i), fun i => ?_, ?_⟩
    · exact ok_natCast_mul _ (hO.2.2.2.2.2.2.1 y hy (x i) (hx i))
    · conv_lhs => rw [hy']
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [smul_smul, hr i, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      congr 1
      ring
  · exact (Fintype.linearIndependent_iff.1 hli) c hc i

theorem latInt_translate : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  intro q _ ι δ₀ θ Ω g S e t hPer hO hS hth halg ht hLe
  obtain ⟨hIsTh, -, hδ, hall, hΩ, hLaws, -⟩ := hPer
  have hp : S.d.Prime := hO.1
  have h7 : S.d % 16 = 7 := hO.2.1
  have hq : q.Prime := Fact.out
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  have hlam : ∀ z : Qbar, ι (z : ℂ) = lam z := fun z => rfl
  have hqd : ¬ q ∣ S.d := (GlobalTheory.MomOne.okArith S.d q ι hp h7 hS).2.2.2.2.2.2
  obtain ⟨x, a, hx, hb, ha⟩ := GlobalTheory.MomOne.exists_orthFrame q g S hq hO hqd
  have hNN := nnBasis_of_frame q S hO x a hx hb ha
  obtain ⟨N, hN⟩ := GlobalTheory.MomOne.Translates.moments_of_translates S.d q lam δ₀ θ ι Ω hp h7 hS hIsTh hδ hall hlam hΩ
    hLaws g S rfl hO g x hNN e hth halg
  have h0 : S.PrimeTo q 0 := ⟨1, one_pos, Nat.coprime_one_left q, by simp [S.La.zero_mem]⟩
  obtain ⟨μ0, hμ0, hM0⟩ := hN 0 h0
  obtain ⟨μt, hμt, hMt⟩ := hN t ht
  have hU0 : opU S.Hm 0 e = e := by funext z; simp [opU, hf]
  have b0 := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x 0 (opU S.Hm 0 e) μ0 hlam hδ hΩ hO hS hNN h0
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm 0 hth.1) hM0
  have bt := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x t (opU S.Hm t e) μt hlam hδ hΩ hO hS hNN ht
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm t hth.1) hMt
  rw [hU0] at b0
  have hN1 : N ≤ 1 := hμ0 ▸ b0.2 hLe
  exact bt.1 (hμt ▸ hN1)

end GlobalTheory.MomTrans
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegralityStatement

section

@[expose] public section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  first | exact @GlobalTheory.MomTrans.latInt_translate | exact GlobalTheory.MomTrans.latInt_translate | (intros; apply GlobalTheory.MomTrans.latInt_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaTranslatesPrimeToQIntegral

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open Formalism.L2.Th1.F (herm altE cmTheta)
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.MomN

def latOne (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  L.lattice.comap (LinearMap.proj 0 : (Fin 1 → ℂ) →ₗ[ℤ] ℂ)

def setupOne (d : ℕ) (L : PeriodPair) : JMB.Setup 1 := ⟨d, hOne L (Fin 1), latOne L⟩

theorem hf_hOne (L : PeriodPair) (z w : Fin 1 → ℂ) : JMB.hf (hOne L (Fin 1)) z w = herm L (z 0) (w 0) := by
  simp [JMB.hf, hOne, herm, div_eq_mul_inv]
  ring

theorem opU_hOne (L : PeriodPair) (x : Fin 1 → ℂ) (F : ℂ → ℂ) (z : Fin 1 → ℂ) :
    JMB.opU (hOne L (Fin 1)) x (fun w => F (w 0)) z = Formalism.L2.Th1.F.opU L (x 0) F (z 0) := by
  simp only [JMB.opU, Formalism.L2.Th1.F.opU, hf_hOne, Pi.add_apply]
  congr 3
  ring

theorem area_pos (L : PeriodPair) : 0 < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L

theorem herm_conj (L : PeriodPair) (x y : ℂ) : herm L y x = conj (herm L x y) := by
  simp [herm, mul_comm]

theorem rankOne_base_weight_eq_cmTheta (d : ℕ) : JMB.w0 d = cmTheta 1 d := by
  simp [JMB.w0, JMB.rtd, cmTheta]

theorem opU_contDiff (L : PeriodPair) (s : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s F) := by
  unfold Formalism.L2.Th1.F.opU herm
  fun_prop

theorem jet_one {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) (k : ℕ) (v : Fin k → Fin 1 → ℂ) :
    iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => F (z 0)) 0 v = (∏ j, v j 0) * iteratedDeriv k F 0 := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).iteratedFDeriv_comp_right hF
    (0 : Fin 1 → ℂ) (i := k) (by exact_mod_cast le_top)
  have e : (fun z : Fin 1 → ℂ => F (z 0)) = F ∘ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) := rfl
  rw [e, h, iteratedDeriv_eq_iteratedFDeriv]
  have e2 : (fun j => v j 0) = fun j => (v j 0) • (1 : ℂ) := by funext j; simp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]
  have := (iteratedFDeriv ℂ k F ((0 : Fin 1 → ℂ) 0)).map_smul_univ (fun j => v j 0) (fun _ => (1 : ℂ))
  simpa [smul_eq_mul] using this

section Lat

variable (d : ℕ) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst

theorem beta_mem {x y : ℂ} (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    ((Real.sqrt d / 2 : ℝ) : ℂ) * herm L x y ∈ JMB.OK d := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L x y hx hy
  obtain ⟨m, hm⟩ := Formalism.L2.Th1.F.altEInt L _ y (hst x hx) hy
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have e : herm L (cmTheta 1 d * x) y = cmTheta 1 d * herm L x y := by unfold herm; ring
  simp only [altE] at hk hm
  rw [e, Complex.mul_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk] at hm
  refine ⟨m - k, k, ?_⟩
  rw [rankOne_base_weight_eq_cmTheta]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im]
    push_cast
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk]
    push_cast
    ring

theorem setupOne_ok (hp : d.Prime) (h16 : d % 16 = 7) : (setupOne d L).Ok := by
  refine ⟨hp, h16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : hOne L (Fin 1) = Matrix.diagonal fun _ => (((Formalism.L2.Th1.F.area L : ℝ) : ℂ))⁻¹ := by
      ext i j
      simp [hOne, Matrix.one_apply, Matrix.diagonal_apply]
    show (hOne L (Fin 1)).PosDef
    rw [h, Matrix.posDef_diagonal_iff]
    intro _
    have := area_pos L
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_pos.2 this
  · have hi : Function.Injective (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) := by
      intro a b hab
      ext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      exact congrArg (fun w : L.lattice => (w : ℂ)) hab
    have hc : Continuous (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) :=
      Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _
    exact DiscreteTopology.of_continuous_injective hc hi
  · have htop : Submodule.span ℝ (L.lattice : Set ℂ) = ⊤ := IsZLattice.span_top
    let c : ℂ →ₗ[ℝ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.id
    rw [eq_top_iff]
    intro v _
    have hv : v = c (v 0) := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
    have h0 : v 0 ∈ Submodule.span ℝ (L.lattice : Set ℂ) := by rw [htop]; trivial
    have hmap : (Submodule.span ℝ (L.lattice : Set ℂ)).map c ≤ Submodule.span ℝ ((setupOne d L).La : Set (Fin 1 → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Submodule.subset_span hw
    rw [hv]
    exact hmap (Submodule.mem_map_of_mem h0)
  · intro x hx
    show (JMB.w0 d • x) 0 ∈ L.lattice
    rw [Pi.smul_apply, smul_eq_mul, rankOne_base_weight_eq_cmTheta]
    exact hst _ hx
  · intro x hx y hy
    show ((Real.sqrt d / 2 : ℝ) : ℂ) * JMB.hf (hOne L (Fin 1)) x y ∈ JMB.OK d
    rw [hf_hOne]
    exact beta_mem d L hst hx hy
  · intro y hy
    have key : ∀ w ∈ L.lattice, ∃ m : ℤ, altE L (y 0) w = (m : ℝ) := by
      intro w hw
      obtain ⟨k, hk⟩ := hy (fun _ => w) hw
      refine ⟨-k, ?_⟩
      have e : JMB.hf (setupOne d L).Hm (fun _ => w) y = herm L w (y 0) := hf_hOne L _ _
      rw [e] at hk
      simp only [altE]
      rw [herm_conj L w (y 0), Complex.conj_im, hk]
      push_cast; ring
    exact Formalism.L2.Th1.H.mem_lattice_of_dual L _ (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)

end Lat

theorem mem_Qbar_phi (D : D7) (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact IsAlgebraic.algHom D.host.φ₀.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic x)

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem contDiff_base_even_theta_kernel : ContDiff ℂ ⊤ B.th0 :=
  (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B)).1.contDiff

def eOne (_B : Base D cc δ) : (Fin 1 → ℂ) → ℂ := fun z => _B.th0 (z 0)

theorem eOne_theta : (setupOne D.host.d B.L).IsTheta (eOne B) := by
  refine ⟨(contDiff_base_even_theta_kernel B).comp (by fun_prop), fun x hx => ?_⟩
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  have hc := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (GlobalTheory.FourthRootStd.hst B) (GlobalTheory.FourthRootStd.omega_mem B)
    (GlobalTheory.FourthRootStd.hθ B) (GlobalTheory.FourthRootStd.hθ' B) h8 (x 0) hx
  funext z
  have hfix := Formalism.L2.Th1.H.th0Char_mul_opU_th0_half_period_eq B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B) (x 0) hx (z 0)
  rw [← hc] at hfix
  have hU : JMB.opU (setupOne D.host.d B.L).Hm x (eOne B) z = Formalism.L2.Th1.F.opU B.L (x 0) B.th0 (z 0) :=
    opU_hOne B.L x B.th0 z
  have hb : (JMB.beta (setupOne D.host.d B.L).d (setupOne D.host.d B.L).Hm x x).re = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (x 0) := by
    have : JMB.hf (setupOne D.host.d B.L).Hm x x = herm B.L (x 0) (x 0) := hf_hOne B.L x x
    rw [JMB.beta, this, Complex.re_ofReal_mul]
    rfl
  simp only [JMB.opW]
  rw [hU, hb]
  exact hfix

theorem eOne_algJets (hc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {δ₀ : ℂ} (h0 : δ / δ₀ ∈ Qbar) :
    (setupOne D.host.d B.L).AlgJets δ₀ (eOne B) := by
  intro k ys hy
  have hcc : cc ≠ ⊥ := hc.1
  have hdir : ∀ j, δ₀⁻¹ * ys j 0 ∈ Qbar := by
    intro j
    obtain ⟨s, hs, hmem⟩ := hy j
    have h1 : (s : ℂ) * ys j 0 ∈ lamOf D cc δ := by
      have := (GlobalTheory.FourthRootStd.mem_iff B _).1 hmem
      simpa using this
    obtain ⟨x, -, hx⟩ := ((GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D).2.2.2.2 cc δ hcc).2 _ |>.1 h1
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : δ₀⁻¹ * ys j 0 = (δ / δ₀) * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
      have : ys j 0 = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
        field_simp
        rw [mul_comm]; exact hx
      rw [this]; ring
    rw [e]
    exact mul_mem (mul_mem h0 (mem_Qbar_phi D _)) (inv_mem (natCast_mem _ s))
  have hj := jet_one (contDiff_base_even_theta_kernel B) k (fun j => δ₀⁻¹ • ys j)
  show iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => B.th0 (z 0)) 0 (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [hj]
  refine mul_mem (prod_mem fun j _ => ?_) (GlobalTheory.T.iteratedDeriv_th0_zero_mem_Qbar D cc δ B hc hδ k)
  simpa using hdir j

end Main

theorem latInt_opU_of_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q →
    ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (s : ℂ) (n : ℕ), Nat.Coprime n q →
    (n : ℂ) * s ∈ B.L.lattice → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) (Formalism.L2.Th1.F.opU B.L s B.th0) := by
  intro D cc δ B hc hδ q _ hq2 hj hcop ι δ₀ θ Ω hPer s n hn hs
  obtain ⟨hp, h16, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hOk : (setupOne D.host.d B.L).Ok := setupOne_ok D.host.d B.L (GlobalTheory.FourthRootStd.hst B) hp h16
  have hd0 : δ / δ₀ ∈ Qbar := (GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hc hδ hPer.2.1 q hq2 hcop).1
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : q = 1 := by simpa using hn
      exact absurd this (Fact.out : q.Prime).one_lt.ne'
    · exact h
  have hprime : (setupOne D.host.d B.L).PrimeTo q (fun _ => s) := ⟨n, hnpos, hn, hs⟩
  let p0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let c0 : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
  have hLat : LatInt ι (Ω / ι δ₀) (setupOne D.host.d B.L).La.toAddSubgroup (eOne B) :=
    GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 1 → ℂ) _ (lamOf D cc δ) _ p0 B.th0 (contDiff_base_even_theta_kernel B)
      (fun x hx => ⟨1, Nat.coprime_one_left q, by
        rw [one_smul]; exact (GlobalTheory.FourthRootStd.mem_iff B _).1 hx⟩)
      (GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime D cc δ B hc hδ q hq2 hj hcop ι δ₀ θ Ω hPer)
  have hres := GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality q ι δ₀ θ Ω 1 (setupOne D.host.d B.L) (eOne B) (fun _ => s) hPer hOk
    (Or.inr ⟨hq2, hj⟩) (eOne_theta B) (eOne_algJets B hc hδ hd0) hprime hLat
  have hU : JMB.opU (setupOne D.host.d B.L).Hm (fun _ => s) (eOne B)
      = fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0) := by
    funext z; exact opU_hOne B.L _ B.th0 z
  rw [hU] at hres
  have hcd : ContDiff ℂ ⊤ (fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0)) :=
    (opU_contDiff B.L s (contDiff_base_even_theta_kernel B)).comp (by fun_prop)
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (Fin 1 → ℂ) ℂ _ _ (lamOf D cc δ) c0 _ hcd
    (fun x hx => ⟨1, Nat.coprime_one_left q, by
      rw [one_smul]
      show x ∈ B.L.lattice
      exact (GlobalTheory.FourthRootStd.mem_iff B _).2 hx⟩) hres

end GlobalTheory.MomN
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaTranslatesPrimeToQIntegralStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cm_theta_translates_prime_to_q_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (s : ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) * s ∈ B.L.lattice → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) (Formalism.L2.Th1.F.opU B.L s B.th0) := by
  first | exact @GlobalTheory.MomN.latInt_opU_of_coprime | exact GlobalTheory.MomN.latInt_opU_of_coprime | (intros; apply GlobalTheory.MomN.latInt_opU_of_coprime <;> assumption)
end
end
