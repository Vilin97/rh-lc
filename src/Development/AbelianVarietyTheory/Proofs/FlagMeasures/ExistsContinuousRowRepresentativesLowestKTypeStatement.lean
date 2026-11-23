module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompactStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.invariantExtension_integrableOn_compact : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ, ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧ ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.LocalL2Isometry.ext_integrableOn | exact GlobalTheory.LocalL2Isometry.ext_integrableOn | (intros; apply GlobalTheory.LocalL2Isometry.ext_integrableOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousConv

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ConvContRep

theorem continuous_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) (ψ f : G → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hf : AEStronglyMeasurable f μ) (hi : ∀ C, IsCompact C → IntegrableOn f C μ) :
    Continuous fun x => ∫ z, ψ (x⁻¹ * z) * f z ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  set L : Set G := (fun p : G × G => p.1 * p.2) '' (K ×ˢ tsupport ψ) with hLdef
  have hL : IsCompact L := (hK.prod hc.isCompact).image continuous_mul
  refine continuousAt_of_dominated
    (bound := fun z => C * L.indicator (fun z => ‖f z‖) z) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hψ.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable).mul hf
  · filter_upwards [hKx] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · have h0 : ψ (x⁻¹ * z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hm => hz ?_
        exact ⟨(x, x⁻¹ * z), ⟨hx, hm⟩, mul_inv_cancel_left x z⟩
      simp [h0, Set.indicator_of_notMem hz]
  · exact (IntegrableOn.integrable_indicator (hi _ hL).norm hL.isClosed.measurableSet).const_mul C
  · refine Filter.Eventually.of_forall fun z => ?_
    have hz : Continuous fun x : G => ψ (x⁻¹ * z) * f z := by fun_prop
    exact hz.continuousAt

theorem conv_isContRep : ∀ (B : RowsAut) (ψ : B.I.GA → ℂ) (F : B.I.L2 B.μf B.fund), Continuous ψ → HasCompactSupport ψ → IsContRep B (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf)) (fun x => ∫ z, ψ (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) := by
  intro B ψ F hψ hc
  obtain ⟨iT2, iLC, iSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have iK : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  obtain ⟨hl, -, -, -, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have iL : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨-, -, hiso, hcontR, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hEinv, hEm⟩ := hext F
  unfold IsContRep
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_conv _ ψ _ hψ hc hEm fun C hC => ((GlobalTheory.T.invariantExtension_integrableOn_compact B C hC).choose_spec F).1
  · intro γ hγ x
    calc ∫ z, ψ ((γ * x)⁻¹ * z) * B.I.ext F z ∂B.I.muA B.μf
        = ∫ w, ψ ((γ * x)⁻¹ * (γ * w)) * B.I.ext F (γ * w) ∂B.I.muA B.μf :=
          (integral_mul_left_eq_self (fun z => ψ ((γ * x)⁻¹ * z) * B.I.ext F z) γ).symm
      _ = ∫ w, ψ (x⁻¹ * w) * B.I.ext F w ∂B.I.muA B.μf := by
          refine integral_congr_ae ?_
          filter_upwards [hEinv] with w hw
          rw [hw γ hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · have hint : Integrable (fun y => ψ y • B.R y F) (B.I.muA B.μf) :=
      (hψ.smul (hcontR F)).integrable_of_hasCompactSupport hc.smul_right
    have hK : AEStronglyMeasurable (fun p : B.I.GA × B.I.GA => B.I.ext F (p.1 * p.2))
        (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) :=
      hEm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_mul ((B.I.muA B.μf).restrict B.fund) (B.I.muA B.μf))
    have hw := (GlobalTheory.ConvKernel.weak_integral_ae_eq (fun x g => B.I.ext F (x * g)) hK
      (fun g => B.R g F) (fun g => B.R_spec g F) ‖F‖ (fun g => (hiso g F).le) ψ
      (hψ.integrable_of_hasCompactSupport hc) (∫ y, ψ y • B.R y F ∂B.I.muA B.μf)
      (fun u => by rw [← integral_inner (𝕜 := ℂ) hint u]; simp only [inner_smul_right])).2
    filter_upwards [hw] with x hx
    refine hx.trans ?_
    rw [← integral_mul_left_eq_self (fun z => ψ (x⁻¹ * z) * B.I.ext F z) x]
    simp only [inv_mul_cancel_left]

end GlobalTheory.ConvContRep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKTypeStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_average_lowest_KType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  first | exact @GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | exact GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | (intros; apply GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebrStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra : ∀ (B : RowsAut) (A : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (χ : B.I.Gf → ℂ) (ψ : B.I.GA → ℂ) (E : gInf B), ContDiff ℝ ∞ A → HasCompactSupport A → Continuous χ → HasCompactSupport χ → (∀ y, ψ y = A (fun v i j => uMat (y.1 v) i j) * χ y.2) → Continuous ψ ∧ HasCompactSupport ψ ∧ ∃ ψ' : B.I.GA → ℂ, Continuous ψ' ∧ HasCompactSupport ψ' ∧ ∀ F : B.I.L2 B.μf B.fund, HasDerivAt (fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0 ∧ ∀ x : B.I.GA, HasDerivAt (fun t : ℝ => ∫ z, ψ ((x * ((fun v => expU (t • E v)), 1))⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0 := by
  first | exact @GlobalTheory.ConvDeriv.convolution_hasDerivAt | exact GlobalTheory.ConvDeriv.convolution_hasDerivAt | (intros; apply GlobalTheory.ConvDeriv.convolution_hasDerivAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKType

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothRepsType

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

theorem exists_level_bump (B : RowsAut) (hg : 1 ≤ B.g) :
    ∃ χ : B.I.Gf → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) ∧
      ∫ k, χ k ∂B.μf = 1 := by
  obtain ⟨hT, -, -, hKc, -, -, hK⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨ho, ⟨K, hKe⟩, -⟩ := hK B.g hg
  have hcl : IsClosed (B.I.Kg B.g) := by
    rw [← hKe] at ho ⊢
    exact K.isClosed_of_isOpen ho
  have hc : IsCompact (B.I.Kg B.g) := hKc.of_isClosed_subset hcl fun x hx => hx.1
  have hne : (B.I.Kg B.g).Nonempty := by
    rw [← hKe]; exact ⟨1, K.one_mem⟩
  have hpos : 0 < B.μf.real (B.I.Kg B.g) :=
    ENNReal.toReal_pos (ho.measure_pos B.μf hne).ne' hc.measure_lt_top.ne
  refine ⟨(B.I.Kg B.g).indicator fun _ => (((B.μf.real (B.I.Kg B.g))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
  · intro k hk
    exact Set.mem_of_indicator_ne_zero hk
  · rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

theorem integrable_of_prod (B : RowsAut) (hσ : IsURep B.σs) (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ)
    (h1 : ∫ k, χ k ∂B.μf = 1) (hc : Continuous fun y : B.I.GA => a y.1 * χ y.2)
    (hs : HasCompactSupport fun y : B.I.GA => a y.1 * χ y.2) (w : B.Hs) :
    Integrable (fun g => a g • B.σs g w) (muInf B.I) := by
  obtain ⟨k, hk⟩ : ∃ k, χ k ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at h1
  have hac : Continuous a := by
    have h2 : Continuous fun g : B.I.Ginf => a g * χ k :=
      hc.comp (f := fun g : B.I.Ginf => ((g, k) : B.I.GA)) (Continuous.prodMk_left k)
    have h3 := h2.mul_const (χ k)⁻¹
    simpa [mul_assoc, mul_inv_cancel₀ hk] using h3
  have has : HasCompactSupport a := by
    refine HasCompactSupport.intro (hs.isCompact.image continuous_fst) fun g hg => ?_
    by_contra h0
    exact hg ⟨(g, k), subset_tsupport _ (mul_ne_zero h0 hk), rfl⟩
  have : IsFiniteMeasureOnCompacts (muInf B.I) := by unfold muInf; infer_instance
  exact (hac.smul (hσ.2.2.2 w)).integrable_of_hasCompactSupport has.smul_right

theorem conv_avg (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : T ∈ B.I.HomS B.σs B.μf B.fund B.R) (hk : ∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u)
    (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ) (hχ : ∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) (h1 : ∫ k, χ k ∂B.μf = 1)
    (w : B.Hs) (hint : Integrable (fun g => a g • B.σs g w) (muInf B.I)) :
    ∫ y, (a y.1 * χ y.2) • B.R y (T w) ∂(B.I.muA B.μf) = T (∫ g, a g • B.σs g w ∂(muInf B.I)) := by
  have : SigmaFinite (muInf B.I) := by unfold muInf; infer_instance
  obtain ⟨-, hmul, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have hpt : ∀ y : B.I.GA, (a y.1 * χ y.2) • B.R y (T w) = χ y.2 • T (a y.1 • B.σs y.1 w) := by
    rintro ⟨g, k⟩
    by_cases h0 : χ k = 0
    · simp [h0]
    · have e1 : B.R (g, k) (T w) = T (B.σs g w) := by
        have : ((g, k) : B.I.GA) = (g, 1) * (1, k) := by simp
        rw [this, hmul, ContinuousLinearMap.mul_apply, hk w k (hχ k h0)]
        exact (congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S w) (hT g)).symm
      simp only [e1, map_smul, smul_smul, mul_comm]
  simp_rw [hpt]
  change ∫ y : B.I.Ginf × B.I.Gf, χ y.2 • T (a y.1 • B.σs y.1 w) ∂((muInf B.I).prod B.μf) = _
  rw [← integral_prod_swap]
  have := integral_prod_smul (μ := B.μf) (ν := muInf B.I) χ (fun g => T (a g • B.σs g w))
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [this, h1, one_smul, T.integral_comp_comm hint]

theorem repsExist : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v))
      (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g →
    ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) →
      ∃ Fr, IsReps B T Fr := by
  intro B d hd h1 hg T hT hk
  classical
  obtain ⟨χ, hχc, hχs, hχK, hχ1⟩ := exists_level_bump B hg
  obtain ⟨huniq, -, htr, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hd).1
  let Fr : B.Hs → B.I.GA → ℂ := fun u => if h : ∃ f, IsContRep B (T u) f then h.choose else 0
  have hFr : ∀ u f, IsContRep B (T u) f → Fr u = f := by
    intro u f hf
    have h : ∃ f, IsContRep B (T u) f := ⟨f, hf⟩
    have : Fr u = h.choose := dif_pos h
    rw [this]
    exact huniq _ _ _ h.choose_spec hf
  refine ⟨Fr, fun P u hu => ?_⟩
  obtain ⟨A, hA, hAs, hfix⟩ := GlobalTheory.T.exists_smooth_average_lowest_KType B d hd h1 P u hu
  let ψ : B.I.GA → ℂ := fun y => A (fun v i j => uMat (y.1 v) i j) * χ y.2
  have hder := fun E => GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra B A χ ψ E hA hAs hχc hχs (fun _ => rfl)
  have hψ : ∫ y, ψ y • B.R y (T (B.tens B.w)) ∂(B.I.muA B.μf) = T u := by
    rw [hfix]
    exact conv_avg B T hT hk (fun g => A (fun v i j => uMat (g v) i j)) χ hχK hχ1 _
      (integrable_of_prod B hσ (fun g => A (fun v i j => uMat (g v) i j)) χ hχ1 (hder 0).1 (hder 0).2.1 _)
  have hrep := GlobalTheory.ConvContRep.conv_isContRep B ψ (T (B.tens B.w)) (hder 0).1 (hder 0).2.1
  rw [hψ] at hrep
  have hFu := hFr u _ hrep
  have hrep' : IsContRep B (T u) (Fr u) := by rw [hFu]; exact hrep
  refine ⟨hrep', fun k hkK y => ?_, fun E y => ?_⟩
  · have := htr _ _ (1, k) hrep'
    rw [hk u k hkK] at this
    exact congrFun (huniq _ _ _ this hrep') y
  · obtain ⟨-, -, ψ', hc', hs', hd'⟩ := hder E
    obtain ⟨hd1, hd2⟩ := hd' (T (B.tens B.w))
    rw [hψ] at hd1
    obtain ⟨A', -, -, hA'⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B A E (B.tens B.w) hσ hA hAs
    rw [← hfix] at hA'
    have hdiff : HasDerivAt (orbit B E u) (dAct B E u) 0 := hA'.differentiableAt.hasDerivAt
    have hd3 : HasDerivAt (fun t : ℝ => T (orbit B E u t)) (T (dAct B E u)) 0 :=
      (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hdiff
    have hfun : (fun t : ℝ => T (orbit B E u t)) =
        fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (T u) := by
      funext t
      exact congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S u) (hT _)
    rw [hfun] at hd3
    have heq := hd3.unique hd1
    have hrep2 := GlobalTheory.ConvContRep.conv_isContRep B ψ' (T (B.tens B.w)) hc' hs'
    rw [← heq] at hrep2
    rw [hFr _ _ hrep2, hFu]
    exact hd2 y

end GlobalTheory.SmoothRepsType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKTypeStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) → ∃ Fr, IsReps B T Fr := by
  first | exact @GlobalTheory.SmoothRepsType.repsExist | exact GlobalTheory.SmoothRepsType.repsExist | (intros; apply GlobalTheory.SmoothRepsType.repsExist <;> assumption)
end
end
