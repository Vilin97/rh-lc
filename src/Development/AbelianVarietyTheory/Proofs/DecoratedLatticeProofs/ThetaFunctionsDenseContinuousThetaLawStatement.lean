module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergAverageCompactSymplecticTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTriviaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_small_compact_level_symplecticCharacter_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  first | exact @GlobalTheory.SmallLevel.exists_small_level | exact GlobalTheory.SmallLevel.exists_small_level | (intros; apply GlobalTheory.SmallLevel.exists_small_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergAverageRealPlacesSmooth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisAverage

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem contDiff_integral_kernel {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [MeasurableSpace R] [BorelSpace R] (μ : Measure R) [μ.IsAddHaarMeasure]
    (φ : R → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (K : R → R → ℂ)
    (hK : ContDiff ℝ ∞ fun p : R × R => K p.1 p.2) (G : R → ℂ) (hG : Continuous G) :
    ContDiff ℝ ∞ fun y => ∫ x, (φ x : ℂ) * K y x * G (y + x) ∂μ := by
  set g : R → R → ℂ := fun p v => (φ (-v) : ℂ) * K p (-v) with hgdef
  have e : ∀ y, ∫ x, (φ x : ℂ) * K y x * G (y + x) ∂μ = convolution G (g y) (ContinuousLinearMap.mul ℝ ℂ) μ y := by
    intro y
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply', g, neg_sub]
    rw [← integral_sub_right_eq_self (fun x => (φ x : ℂ) * K y x * G (y + x)) y]
    congr 1
    funext x
    rw [add_comm y (x - y), sub_add_cancel]
    ring
  have hk : IsCompact (Neg.neg '' tsupport φ) := hφc.isCompact.image continuous_neg
  have hgs : ∀ p, ∀ x, p ∈ (Set.univ : Set R) → x ∉ Neg.neg '' tsupport φ → g p x = 0 := by
    intro p x _ hx
    have : -x ∉ tsupport φ := fun h => hx ⟨-x, h, neg_neg x⟩
    simp [g, image_eq_zero_of_notMem_tsupport this]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿g) (Set.univ ×ˢ Set.univ) := by
    apply ContDiff.contDiffOn
    exact (Complex.ofRealCLM.contDiff.comp (hφ.comp contDiff_snd.neg)).mul
      (hK.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hc := contDiffOn_convolution_right_with_param_comp (μ := μ) (ContinuousLinearMap.mul ℝ ℂ)
    (s := Set.univ) (v := id) contDiffOn_id isOpen_univ hk hgs hG.locallyIntegrable hg
  rw [funext e]
  exact contDiffOn_univ.1 hc

theorem sm_heisO_average : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (φ : GlobalTheory.FockCompare.RW T A → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ (f : WO A T → ℂ), Continuous f → GlobalTheory.FockCompare.Sm (GlobalTheory.FockCompare.iotaW σ T A) (fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (GlobalTheory.FockCompare.iotaW σ T A x) f w) := by
  intro D θ σ h ψ hψ A T φ hφ hφc f hf w
  haveI : (volume : Measure (Fin A.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin T.rank → Fin A.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let Bc : RW T A →L[ℝ] RW T A →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (RW T A →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (RW T A →L[ℝ] ℝ)).toLinearMap ∘ₗ omO A T)
  have hK : ContDiff ℝ ∞ fun p : RW T A × RW T A =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (Bc (piW θ T A w + p.1) p.2))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((Bc.contDiff.comp (contDiff_const.add contDiff_fst)).clm_apply contDiff_snd)))
  have hG : Continuous fun t : RW T A => f (w + iotaW σ T A t) :=
    hf.comp (continuous_const.add (h.continuous_iota T A))
  have key := contDiff_integral_kernel (volume : Measure (RW T A)) φ hφ hφc
    (fun y x => Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (Bc (piW θ T A w + y) x)))) hK _ hG
  refine (congrArg (ContDiff ℝ ∞) ?_).mp key
  funext y
  refine congrArg _ ?_
  funext x
  rw [heisO_iota h hψ, map_add (piW θ T A), h.pi_iota, map_add (iotaW σ T A), ← add_assoc, mul_assoc]
  rfl

end GlobalTheory.HeisAverage
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergAverageRealPlacesSmoothStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.heisenbergAverage_realPlaces_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (φ : GlobalTheory.FockCompare.RW T A → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ (f : WO A T → ℂ), Continuous f → GlobalTheory.FockCompare.Sm (GlobalTheory.FockCompare.iotaW σ T A) (fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (GlobalTheory.FockCompare.iotaW σ T A x) f w) := by
  first | exact @GlobalTheory.HeisAverage.sm_heisO_average | exact GlobalTheory.HeisAverage.sm_heisO_average | (intros; apply GlobalTheory.HeisAverage.sm_heisO_average <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaLawTendstoUniformNearZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisNearZero

theorem heisO_near_zero_unif : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ N ∈ 𝓝 (0 : WO A T), ∀ a ∈ N, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ ε := by
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hc : Continuous ψ := hψ.1.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  let Φ : WO A T × WO A T → ℂ := fun p => heisO ψ A T p.1 q p.2 - q p.2
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : WO A T × WO A T => symplOH A T p.2 p.1 :=
      GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd continuous_fst
    exact ((hc.comp h1).mul (hq.comp (continuous_snd.add continuous_fst))).sub (hq.comp continuous_snd)
  have hΦ0 : ∀ w, Φ (0, w) = 0 := by
    intro w
    simp only [Φ, heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero, sub_self]
  have hev : ∀ᶠ a in 𝓝 (0 : WO A T), ∀ w ∈ K, ‖Φ (a, w)‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun w _ => ?_
    have ht : Filter.Tendsto Φ (𝓝 ((0 : WO A T), w)) (𝓝 0) := by
      have := hΦ.tendsto ((0 : WO A T), w); rwa [hΦ0] at this
    exact (ht.norm.eventually (gt_mem_nhds (by simpa using hε))).mono fun z hz => by simpa using hz
  refine ⟨_, hev, fun a ha w => ?_⟩
  obtain ⟨g, hg, hgw⟩ := hKc w
  obtain ⟨γ, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hg
  have e : Φ (a, GlobalTheory.MixModel.rat γ + w) = ψ (-(symplOH A T (ratW T A γ) w)) * Φ (a, w) := by
    simp only [Φ]
    rw [← GlobalTheory.MixModel.ratW_eq, GlobalTheory.OrientedHeis.heisO_quasi a q hlaw γ w, hlaw γ w, mul_sub]
  have h := ha _ hgw
  rw [e, norm_mul, hn, one_mul] at h
  exact h.le

end GlobalTheory.HeisNearZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaLawTendstoUniformNearZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.heisenbergOperator_thetaLaw_tendsto_uniform_near_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ N ∈ 𝓝 (0 : WO A T), ∀ a ∈ N, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ ε := by
  first | exact @GlobalTheory.HeisNearZero.heisO_near_zero_unif | exact GlobalTheory.HeisNearZero.heisO_near_zero_unif | (intros; apply GlobalTheory.HeisNearZero.heisO_near_zero_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLaw

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisSmoothing

open GlobalTheory.FockCompare

theorem norm_integral_sub_le {X : Type} [MeasurableSpace X] (μ : Measure X) (φ : X → ℝ) (F : X → ℂ) (c : ℂ) (δ : ℝ)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∫ x, φ x ∂μ = 1) (hφ : Integrable φ μ) (hF : Integrable (fun x => (φ x : ℂ) * F x) μ)
    (hb : ∀ x, φ x ≠ 0 → ‖F x - c‖ ≤ δ) : ‖∫ x, (φ x : ℂ) * F x ∂μ - c‖ ≤ δ := by
  have hc : Integrable (fun x => (φ x : ℂ) * c) μ := hφ.ofReal.mul_const c
  have e : ∫ x, (φ x : ℂ) * c ∂μ = c := by
    rw [integral_mul_const, integral_complex_ofReal, h1]
    simp
  have e2 : ∫ x, φ x * δ ∂μ = δ := by rw [integral_mul_const, h1, one_mul]
  rw [← e2]
  conv_lhs => rw [← e, ← integral_sub hF hc]
  refine norm_integral_le_of_norm_le (hφ.mul_const δ) (Filter.Eventually.of_forall fun x => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x)]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hb x hx) (h0 x)

theorem isAddHaarMeasure_volume (ι m n : Type) [Fintype ι] [Fintype m] [Fintype n] :
    (volume : Measure (ι → m → n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (m → n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem exists_theta_of_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (f : WO A T → ℂ), Continuous f → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), f (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * f u) → (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u f = f) → ∀ N ∈ 𝓝 (0 : WO A T), ∀ δ : ℝ, (∀ a ∈ N, ∀ w, ‖heisO ψ A T a f w - f w‖ ≤ δ) → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ w, ‖g w - f w‖ ≤ δ := by
  intro D ψ hψ A T f hf hlaw hlev N hN δ hδ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -⟩ := lattice_Mx D T.rank A.rank
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := isAddHaarMeasure_volume _ _ _
  have hι : Continuous (iotaW σ T A) := h.continuous_iota T A
  have hN' : iotaW σ T A ⁻¹' N ∈ 𝓝 (0 : RW T A) :=
    hι.continuousAt.preimage_mem_nhds (by rw [AddMonoidHom.map_zero]; exact hN)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN'
  let b : ContDiffBump (0 : RW T A) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let φ : RW T A → ℝ := b.normed volume
  have hφs : ContDiff ℝ ∞ φ := b.contDiff_normed
  have hφc : HasCompactSupport φ := b.hasCompactSupport_normed
  let g : WO A T → ℂ := fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
  have hsm : Sm (iotaW σ T A) g := GlobalTheory.T.heisenbergAverage_realPlaces_smooth D θ σ h ψ hψ A T φ hφs hφc f hf
  have hl : ∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u g = g := by
    obtain ⟨U, hU, hUf⟩ := hlev
    refine ⟨U, hU, fun u hu h0 => funext fun w => ?_⟩
    show ψ (symplOH A T w u) * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (w + u) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e := congrFun (GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (h.real_iota T A x) (hUf u hu h0)) w
    show _ = (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← e]
    exact mul_left_comm _ _ _
  refine ⟨g, ⟨fun γ w => ?_, hl, GlobalTheory.OrientedHeis.continuous_of_level h hψ.1.1 g hl hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T A).1 g).2 hsm⟩, fun w => ?_⟩
  · show ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) =
      _ * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) = _
    rw [GlobalTheory.OrientedHeis.heisO_quasi _ f hlaw]
    exact mul_left_comm _ _ _
  · have hc : Continuous fun x : RW T A => heisO ψ A T (iotaW σ T A x) f w :=
      (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_const hι)).mul
        (hf.comp (continuous_const.add hι))
    have hφℂ : HasCompactSupport fun x => (φ x : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
    refine norm_integral_sub_le volume φ _ (f w) δ b.nonneg_normed b.integral_normed b.integrable_normed
      (((Complex.continuous_ofReal.comp hφs.continuous).mul hc).integrable_of_hasCompactSupport hφℂ.mul_right)
      fun x hx => hδ _ (hrN ?_) w
    have : x ∈ Function.support φ := hx
    rwa [b.support_normed_eq] at this

theorem exists_theta_near : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  have h1 := GlobalTheory.T.heisenbergOperator_thetaLaw_tendsto_uniform_near_zero
  have h2a := GlobalTheory.T.exists_small_compact_level_symplecticCharacter_trivial
  have h2b := GlobalTheory.T.exists_heisenbergAverage_compactSymplecticTrivial
  have h4 := exists_theta_of_level
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨N, hN, hNq⟩ := h1 D ψ hψ A T q hq hlaw (ε / 2) (half_pos hε)
  obtain ⟨K, hKc, hKN, -, ⟨U, hU, hUK⟩, hKψ⟩ := h2a D ψ hψ A T N hN
  obtain ⟨g1, hg1c, hg1law, hg1K, hg1near⟩ := h2b D ψ hψ A T K hKc hKψ q hq hlaw
  have hg1q : ∀ w, ‖g1 w - q w‖ ≤ ε / 2 := hg1near (ε / 2) (fun a ha w => hNq a (hKN ha) w)
  obtain ⟨N2, hN2, hN2g⟩ := h1 D ψ hψ A T g1 hg1c hg1law (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgg1⟩ := h4 D ψ hψ A T g1 hg1c hg1law ⟨U, hU, fun u hu h0 => hg1K u (hUK u hu h0)⟩ N2 hN2 (ε / 2) hN2g
  refine ⟨g, hg, fun w => ?_⟩
  have e : q w - g w = (g1 w - g w) - (g1 w - q w) := by ring
  rw [e]
  calc ‖(g1 w - g w) - (g1 w - q w)‖ ≤ ‖g1 w - g w‖ + ‖g1 w - q w‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [norm_sub_rev]; exact hgg1 w
        · exact hg1q w
    _ = ε := add_halves ε

end GlobalTheory.HeisSmoothing

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLawStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.theta_functions_dense_continuous_theta_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  first | exact @GlobalTheory.HeisSmoothing.exists_theta_near | exact GlobalTheory.HeisSmoothing.exists_theta_near | (intros; apply GlobalTheory.HeisSmoothing.exists_theta_near <;> assumption)
end
end
