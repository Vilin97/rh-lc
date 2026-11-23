module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZero

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem etale_norm_continuous_and_zero (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := by
  classical
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  let b0 := Module.finBasisOfFinrankEq F E h2
  let b : Module.Basis (Fin 2) A.K A.L := hb.basis b0
  have hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det := fun y => Algebra.norm_eq_matrix_det b y
  refine ⟨?_, ?_⟩
  · have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := funext hN
    rw [this]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let f : A.L →ₗ[F] A.K := ((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine hf.congr fun y => ?_
    simp [f, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [hN, map_zero]
    simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZeroStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Continuous A.NL ∧ A.NL 0 = 0 := by
  first | exact @GlobalTheory.etale_norm_continuous_and_zero | exact GlobalTheory.etale_norm_continuous_and_zero | (intros; apply GlobalTheory.etale_norm_continuous_and_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn

section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement

section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInduced

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WeilSmooth

def lS {k : Type} [CommRing k] (u : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; u, 1], by simp [Matrix.det_fin_two]⟩

theorem sl_ext {k : Type} [CommRing k] {A B : SpecialLinearGroup (Fin 2) k}
    (h : (A : Matrix (Fin 2) (Fin 2) k) = B) : A = B := Subtype.ext h

theorem lS_eq {k : Type} [CommRing k] (u : k) : lS u = (wS k)⁻¹ * nS (-u) * wS k := by
  apply sl_ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lS, nS, wS, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem mid_eq {k : Type} [CommRing k] (a a' t t' : k) (ha : a * a' = 1) (ht : t * t' = 1) :
    ((nS ((a - 1) * t') * lS t * nS ((a' - 1) * t') * lS (-(t * a)) : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a'] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (a-1)*ht - t*a*((a-1)*(a'-1)*t'*ht + t'*ha)
  · linear_combination (a-1)*(a'-1)*t' * ht + t' * ha
  · linear_combination (-t*a*(a'-1))*ht - t*ha
  · linear_combination (a'-1)*ht

theorem decomp {k : Type} [CommRing k] (g : SpecialLinearGroup (Fin 2) k) (a' t t' : k)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * a' = 1) (ht : t * t' = 1) :
    g = lS ((g : Matrix (Fin 2) (Fin 2) k) 1 0 * a') * (nS (((g : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) * t') * lS t *
      nS ((a' - 1) * t') * lS (-(t * (g : Matrix (Fin 2) (Fin 2) k) 0 0))) *
      nS ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * a') := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mid_eq _ _ _ _ ha ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 0 1) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0 * (g : Matrix (Fin 2) (Fin 2) k) 0 1 * a' +
      (g : Matrix (Fin 2) (Fin 2) k) 1 1) * ha + a' * hdet

end GlobalTheory.WeilSmooth

noncomputable section
namespace GlobalTheory.WeilSmooth
open GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem nl_cont [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero F E A
theorem inv_cont (A : Et F E) : (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse F E A

theorem fix_n [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ z in 𝓝 (0 : A.K), W (nS z) f = f := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun p : A.K × A.L => ‖Algebra.trace F A.K (p.1 * x * A.NL p.2)‖ :=
    (htr.comp ((continuous_fst.mul continuous_const).mul ((nl_cont A).1.comp continuous_snd))).norm
  have hK : IsCompact (tsupport f) := hf.2
  have hev : ∀ᶠ z in 𝓝 (0 : A.K), ∀ y ∈ tsupport f, ‖Algebra.trace F A.K (z * x * A.NL y)‖ < 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖Algebra.trace F A.K ((0 : A.K) * x * A.NL y)‖ < 1 := by simp
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h0)
  filter_upwards [hev] with z hz
  funext y
  rw [(hW.2 f hf).1 z y]
  by_cases hy : y ∈ tsupport f
  · rw [Et.psiK, hψ.1 _ (hz y hy).le, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

theorem fix_l [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ u in 𝓝 (0 : A.K), W (lS u) f = f := by
  have h1 := fix_n A ψ hψ x ω μ γ W hW (W (wS A.K) f) (hW.1.1 _ _ hf)
  have h2 : Tendsto (fun u : A.K => -u) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0 : A.K))
  filter_upwards [h2.eventually h1] with u hu
  have hwf := hW.1.1 (wS A.K) f hf
  calc W (lS u) f = W ((wS A.K)⁻¹ * nS (-u) * wS A.K) f := by rw [lS_eq]
    _ = W (wS A.K)⁻¹ (W (nS (-u)) (W (wS A.K) f)) := by
        rw [hW.1.2.2.1 _ _ _ hf, hW.1.2.2.1 _ _ _ hwf]
    _ = W ((wS A.K)⁻¹ * wS A.K) f := by rw [hu, hW.1.2.2.1 _ _ _ hf]
    _ = f := by rw [inv_mul_cancel, hW.1.2.1 _ hf]

theorem jx_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  intro F E _ _ _ _ _ A ψ hψ x μ γ W hW φ hφ
  obtain ⟨⟨htest, hone, hmul, hlin⟩, hact⟩ := id hW
  have ht0 : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have h0 : ∀ g, W g 0 = 0 := by
    intro g
    have := hlin g (-1) 0 0 ht0 ht0
    simpa using this
  have hfix : ∀ g h, W h φ = φ → W (g * h) φ = W g φ := fun g h hh => by rw [hmul _ _ _ hφ, hh]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hn := fix_n A ψ hψ x A.etaK μ γ W hW φ hφ
    have hl := fix_l A ψ hψ x A.etaK μ γ W hW φ hφ
    obtain ⟨hunit, hinv⟩ := inv_cont A
    have hQ : ∀ᶠ u in 𝓝 (0 : A.K), ∀ᶠ v in 𝓝 u, W (lS v) φ = φ := hl.eventually_nhds
    haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
    have hcm : Continuous (algebraMap F A.K) := continuous_algebraMap F A.K
    have hQ2 : ∀ᶠ c in 𝓝 (0 : F), (∀ᶠ v in 𝓝 (algebraMap F A.K c), W (lS v) φ = φ) ∧
        ∀ᶠ v in 𝓝 (-algebraMap F A.K c), W (lS v) φ = φ := by
      have e1 : Tendsto (algebraMap F A.K) (𝓝 0) (𝓝 0) := by simpa using hcm.tendsto 0
      have e2 : Tendsto (fun c => -algebraMap F A.K c) (𝓝 0) (𝓝 0) := by simpa using (hcm.tendsto 0).neg
      exact (e1.eventually hQ).and (e2.eventually hQ)
    haveI := NormedField.nhdsNE_neBot (0 : F)
    obtain ⟨c, ⟨hc1, hc2⟩, hc0⟩ := ((hQ2.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {y : F | y ≠ 0} ∈ 𝓝[≠] (0 : F))).exists
    set t := algebraMap F A.K c with ht_def
    set t' := algebraMap F A.K c⁻¹ with ht'_def
    have htt : t * t' = 1 := by rw [ht_def, ht'_def, ← map_mul, mul_inv_cancel₀ hc0, map_one]
    have hq1 : Tendsto (fun q : A.K × A.K × A.K => q.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      continuous_fst.tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have ha : Tendsto (fun q : A.K × A.K × A.K => 1 + q.1) (𝓝 (0, 0, 0)) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : A.K))).add hq1
    have hi : Tendsto (fun q : A.K × A.K × A.K => Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 1) := by
      have := hinv.tendsto.comp ha
      rw [Ring.inverse_one] at this
      exact this
    have hq2 : Tendsto (fun q : A.K × A.K × A.K => q.2.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_fst.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have hq3 : Tendsto (fun q : A.K × A.K × A.K => q.2.2) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_snd.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have key : ∀ᶠ q : A.K × A.K × A.K in 𝓝 (0, 0, 0), IsUnit (1 + q.1) ∧
        W (lS (q.2.2 * Ring.inverse (1 + q.1))) φ = φ ∧ W (nS (q.1 * t')) φ = φ ∧
        W (nS ((Ring.inverse (1 + q.1) - 1) * t')) φ = φ ∧ W (lS (-(t * (1 + q.1)))) φ = φ ∧
        W (nS (q.2.1 * Ring.inverse (1 + q.1))) φ = φ := by
      have f1 : Tendsto (fun q : A.K × A.K × A.K => q.2.2 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq3.mul hi
      have f2 : Tendsto (fun q : A.K × A.K × A.K => q.1 * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq1.mul_const t'
      have f3 : Tendsto (fun q : A.K × A.K × A.K => (Ring.inverse (1 + q.1) - 1) * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using (hi.sub_const 1).mul_const t'
      have f4 : Tendsto (fun q : A.K × A.K × A.K => -(t * (1 + q.1))) (𝓝 (0, 0, 0)) (𝓝 (-t)) := by
        simpa using (ha.const_mul t).neg
      have f5 : Tendsto (fun q : A.K × A.K × A.K => q.2.1 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq2.mul hi
      exact (ha.eventually hunit).and ((f1.eventually hl).and ((f2.eventually hn).and ((f3.eventually hn).and
        ((f4.eventually hc2).and (f5.eventually hn)))))
    rw [nhds_prod_eq, nhds_prod_eq] at key
    obtain ⟨p1, hp1, p2, hp2, h12⟩ := eventually_prod_iff.1 key
    obtain ⟨p3, hp3, p4, hp4, h34⟩ := eventually_prod_iff.1 hp2
    refine ⟨{e | p1 e ∧ p3 e ∧ p4 e}, hp1.and (hp3.and hp4), ?_⟩
    intro g k hk
    have e00 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1 := by simp
    have e01 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 1 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 1 := by simp
    have e10 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 1 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 1 0 := by simp
    have k1 := (hk 0 0).1
    have k2 := (hk 0 1).2.1
    have k3 := (hk 1 0).2.2
    rw [e00] at k1
    rw [e01] at k2
    rw [e10] at k3
    obtain ⟨hu, hP1, hP2, hP3, hP4, hP5⟩ := h12 k1 (h34 k2 k3)
    have h1a : (1 : A.K) + ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1) = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 := by ring
    simp only [h1a] at hu hP1 hP2 hP3 hP4 hP5
    have hdec := decomp k (Ring.inverse ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0)) t t'
      (Ring.mul_inverse_cancel _ hu) htt
    have hk : W k φ = φ := by
      rw [hdec, hfix _ _ hP5, hfix _ _ ?_, hP1]
      rw [hfix _ _ hP4, hfix _ _ hP3, hfix _ _ hc1.self_of_nhds, hP2]
    show W (g * k) φ 0 = W g φ 0
    rw [hfix _ _ hk]
  · intro z s g
    have hg := htest g φ hφ
    show W (nS z * mS s * g) φ 0 = A.etaK s * (A.absK s : ℂ) * W g φ 0
    rw [hmul _ _ _ hφ, hmul _ _ _ hg, (hact _ (htest _ _ hg)).1 z 0, (hact _ hg).2.1 s 0, smul_zero,
      (nl_cont A).2]
    simp [Et.psiK]
  · intro hne hγ
    apply hne
    have hw : W (wS A.K) φ = 0 := funext fun y => by rw [(hact φ hφ).2.2 y, hγ, zero_mul]; rfl
    calc φ = W 1 φ := (hone φ hφ).symm
      _ = W ((wS A.K)⁻¹ * wS A.K) φ := by rw [inv_mul_cancel]
      _ = 0 := by rw [hmul _ _ _ hφ, hw, h0]

end GlobalTheory.WeilSmooth
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInducedStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilRep_evalZero_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  first | exact @GlobalTheory.WeilSmooth.jx_mem_induced | exact GlobalTheory.WeilSmooth.jx_mem_induced | (intros; apply GlobalTheory.WeilSmooth.jx_mem_induced <;> assumption)
end
end
