module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsThVEqFK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LamFormula
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PairingK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ParsevalPolK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MapHaar
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisCK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heis_C_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LamFormulaK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem lam_formula_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y)
    (hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) := by
  classical
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  haveI hBor : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable E := GlobalTheory.ThetaParsevalInner.countable_numberField E
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : Countable (ratLF F E nS nT) := by
    refine Function.Surjective.countable
      (f := fun m : Fin nT → Fin nS → E => (⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of m),
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ratLF F E nS nT)) ?_
    rintro ⟨r, m, rfl⟩
    exact ⟨m, rfl⟩
  obtain ⟨Nn, hNn⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).2
    (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
  obtain ⟨h0, htop, -, -⟩ := hNn ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.mpr htop
  haveI := hν
  have hstd := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hstd.1
  refine ⟨((ν 𝓕).toReal : ℂ), ?_, fun Φ hΦ v => ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  set x : Fin N → AF F := α v with hx
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin N → F) → (Fin N → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin N → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : (Fin N → F) → WOF F E nS nT → ℂ, ch = fun ξ u => B.ψ (emb ξ ⬝ᵥ β u) := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have hch_norm : ∀ ξ u, ‖ch ξ u‖ = 1 := fun ξ u => by rw [hch]; exact hnorm _
  have hch_cont : ∀ ξ, Continuous (ch ξ) := fun ξ => by
    rw [hch]; exact hcont.comp (continuous_const.dotProduct hβc)
  have hint : ∀ u : WOF F E nS nT,
      heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)
        (dC (AF F ⊗[F] E) nT * u) = ∑' ξ, a ξ * ch ξ u := by
    intro u
    have h1 : e (dC (AF F ⊗[F] E) nT * u) = (0, β u) := by
      have := hCe u 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    have h2 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    simp only [heisOF, symplOHF, Function.comp_apply, he, h1, h2, hCe, GlobalTheory.ThetaOntoF.algebraMap_half]
    unfold thV GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    rw [← tsum_mul_left]
    congr 1
    funext ξ
    subst ha hch hemb
    simp only [symV, dotProduct_zero, zero_dotProduct, zero_sub]
    exact psi_cancel B.ψ _ _ _
  have hFint : ∀ ξ, Integrable (fun u => a ξ * ch ξ u) (ν.restrict 𝓕) := fun ξ =>
    (Integrable.of_bound (hch_cont _).aestronglyMeasurable 1 (ae_of_all _ fun u => (hch_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ, ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν = ‖a ξ‖ * ν.real 𝓕 := by
    intro ξ
    simp only [norm_mul, hch_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ => ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : Fin N → F, ∫ u in 𝓕, ch ζ u ∂ν = if ζ = 0 then (ν.real 𝓕 : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ u, ch 0 u = 1 := fun u => by simp [hch, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push Not at h; exact hζ (funext h)
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist ν (ratLF F E nS nT) h𝓕 (h := ch ζ) ?_
        (c := β.symm (Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0))) (a := B.ψ s0) ?_ hs0
      · intro r hr u
        obtain ⟨x₀, rfl⟩ := hr
        obtain ⟨η, hη⟩ := hr1 x₀
        have hr' : β ((incAF F E).toAddMonoidHom.mapMatrix x₀) = GlobalTheory.SWQ.rat η := hη
        simp only [hch, map_add (f := _), hr', dotProduct_add, AddChar.map_add_eq_mul]

        rw [show emb ζ ⬝ᵥ GlobalTheory.SWQ.rat η = algebraMap F (AF F) (ζ ⬝ᵥ η) by
        subst hemb; simp [dotProduct, map_sum, map_mul, GlobalTheory.SWQ.rat], htriv, one_mul]
      · intro u
        simp only [hch, map_add (f := _), LinearEquiv.apply_symm_apply, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [integral_const_mul, horth]
  rw [tsum_eq_single 0 (fun ξ hξ => by rw [if_neg hξ, mul_zero])]
  rw [if_pos rfl, ha, hemb]
  have hz : (fun i : Fin N => (0 : AF F)) + x = x := by funext i; simp
  simp only [Pi.zero_apply, map_zero]
  rw [hz, Measure.real]
  ring
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchAFactsK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem schA_facts_k {B : Base F E} {σ : E →ₐ[F] E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (N : ℕ) (μN : Measure (Fin N → AF F))
    (hμN : μN.IsAddHaarMeasure) (Φ : (Fin N → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin N)) :
    Continuous Φ ∧ Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μN ∧
      ∀ b : Fin N → AF F, (fun x => B.ψ (x ⬝ᵥ b) * Φ x) ∈ schA F (Fin N) := by
  refine ⟨GlobalTheory.ThKOp.continuous_of_mem_schA hΦ, ?_, fun b => ?_⟩
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : BorelSpace (AF F) := ⟨rfl⟩
    have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
    have key : ∀ (m : MeasurableSpace (Fin N → AF F)), m = borel _ → ∀ μ : @Measure _ m,
        @Measure.IsAddHaarMeasure _ _ _ m μ → Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μ := by
      rintro m rfl μ hμ
      have hm := GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ
      have hi := (hm.integrable_norm_pow two_ne_zero).ofReal (𝕜 := ℂ)
      refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    exact key _ hb μN hμN
  · have h := GlobalTheory.WeylFour.SchrKeep.schr_mem_schA F B.ψ hB.std (Fin N) (0, b) Φ hΦ
    convert h using 1
    funext x
    simp [GlobalTheory.WeilM.schr]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CoefK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.LagrangianIntegralFactorisation GlobalTheory.ThetaTransform
theorem coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∃ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (κ : ℝ), μW.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < κ ∧
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        Continuous (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ∧ Integrable (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ν ∧
        ∀ y : WOF F E nS nT,
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) f w * starRingEnd ℂ (f w) ∂μW =
            (κ : ℂ) * ∫ v, phase σ JS JT ξ₀ B.ψ y v * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f v ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hstd := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  obtain ⟨N, α, β, e, hCe, he, hrat, hrat', hec, hes, hαc, hαs, hβc, hβs, hr1, hr2⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.coords_k hB hS hT hξ hσ
  obtain ⟨μN, μW, 𝓕W, c₁, hμN, hμW, h𝓕W, hc₁, hpar⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.parseval_pol_k hB N e hec hes hrat hrat'
  obtain ⟨c₀, hc₀, hlam⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.lam_formula_k hB JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he hβc hβs hr1 hr2
  obtain ⟨c₂, hc₂, hmap, hint⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.map_haar α hαc hαs ν hν μN hμN
  have hn0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  refine ⟨μW, 𝓕W, c₁ / (c₂ * ‖c₀‖ ^ 2), hμW, h𝓕W, by positivity, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, rfl⟩ := _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k F E σ B hB nS (nT + nT) JS _ hS hT' ξ₀ hξ hσ hstd N e he hrat f hf
  obtain ⟨hΦc, hΦi, hΦm⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.schA_facts_k hB N μN hμN Φ hΦ
  have hnrm : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (thV B.ψ Φ ∘ e) =
      fun v => ((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v))) := by
    funext v
    unfold nrm
    rw [hlam Φ hΦ v, map_mul, Complex.ofReal_pow, ← Complex.mul_conj' c₀]
    ring
  have hph : ∀ y v, phase σ JS JT ξ₀ B.ψ y v = B.ψ (α v ⬝ᵥ β y) := by
    intro y v
    unfold phase
    rw [he]
    have h1 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    have h2 : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
      have := hCe y 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    rw [h1, h2]
    simp [symV]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [hnrm]
    exact continuous_const.mul ((hΦc.comp hαc).mul (Complex.continuous_conj.comp (hΦc.comp hαc)))
  · rw [hnrm]
    exact ((hint _).2 hΦi).const_mul _
  · rw [_root_.PositivityTheory.ThKW.AdelicSchwartzProperties.heis_C_k hB JS JT ξ₀ N α β e hCe he Φ y]
    have hl : ∫ w in 𝓕W, (thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e) w * starRingEnd ℂ ((thV B.ψ Φ ∘ e) w) ∂μW =
        (c₁ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN :=
      hpar _ (hΦm (β y)) Φ hΦ
    rw [hl, hnrm]
    simp_rw [hph]
    have hr : ∫ v, B.ψ (α v ⬝ᵥ β y) * (((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v)))) ∂ν =
        ((‖c₀‖ ^ 2 : ℝ) : ℂ) * ((c₂ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN) := by
      rw [← hmap (fun x => B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x)), ← integral_const_mul]
      congr 1
      funext v
      ring
    rw [hr]
    have hc2 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
    have hc0 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn0 2).ne'
    have hn' : ((‖c₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end
end
