module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LamFormula
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MapHaar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalAdelicPairFundamental
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalPol

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped Pointwise in
theorem parseval_pol {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS (nT + nT)
  haveI := i1
  haveI := i2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  letI mP : MeasurableSpace (VA F N) := borel _
  haveI : BorelSpace (VA F N) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact PositivityTheory.ThKW.ParsevalPolarization.parseval_adelic_pair_fundamental hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SchAFacts

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schA_facts {B : Base F E} {σ : E →ₐ[F] E} (hB : B.IsGood σ) (N : ℕ) (μN : Measure (Fin N → AF F))
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

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SymplOHF

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heis_C {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
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

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoAlt

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.LagrangianIntegralFactorisation GlobalTheory.ThetaTransform

theorem coef : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
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
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨N, α, β, e, hCe, he, hrat, hrat', hec, hes, hαc, hαs, hβc, hβs, hr1, hr2⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.coords hB hS hT hξ hσ
  obtain ⟨μN, μW, 𝓕W, c₁, hμN, hμW, h𝓕W, hc₁, hpar⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.parseval_pol hB N e hec hes hrat hrat'
  obtain ⟨c₀, hc₀, hlam⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.lam_formula hB JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he hβc hβs hr1 hr2
  obtain ⟨c₂, hc₂, hmap, hint⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.map_haar α hαc hαs ν hν μN hμN
  have hn0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  refine ⟨μW, 𝓕W, c₁ / (c₂ * ‖c₀‖ ^ 2), hμW, h𝓕W, by positivity, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, rfl⟩ := GlobalTheory.ThetaOntoF.exists_thV_eqF F E σ B hB nS (nT + nT) JS _ hS hT' ξ₀ hξ hσ hstd N e he hrat f hf
  obtain ⟨hΦc, hΦi, hΦm⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.schA_facts hB N μN hμN Φ hΦ
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
  · rw [PositivityTheory.ThKW.AdelicSchwartzProperties.heis_C hB JS JT ξ₀ N α β e hCe he Φ y]
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
