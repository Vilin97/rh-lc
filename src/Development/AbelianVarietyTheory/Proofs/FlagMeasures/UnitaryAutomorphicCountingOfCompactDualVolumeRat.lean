module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjPowOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointKernelBoundOfPointwiseBoundStatement
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBoundsStatement
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalRowsSpaceDiscreteSeriesCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalfStatement
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInductionStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKTypeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneTypeArith
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundOfDecGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound

section

@[expose] public section

open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepRegion

theorem one_le_f (I : AutInst) : 1 ≤ I.f := by
  show 0 < Module.finrank ℚ I.F
  exact Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h0 : discr I.E ≠ 0 := discr_ne_zero I.E
    have : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem deepBound (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (hK : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound) :
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  intro Cg hCg
  refine ⟨8, ?_⟩
  intro B d p q b hq hH
  obtain ⟨hDS, hSig, hn0, hqn, hrd, hf, hb, hbb, hlam, hg1, hgb, hg0p, hg0, hsplit, hgap⟩ := id hH
  have hgc : ∀ v, ∃ c : ℝ, 0 < c ∧ IsGauge (B.I.ε v) c := fun v => by
    obtain ⟨c, hc, hc', -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    exact ⟨c, hc, hc'⟩
  choose c hc0 hc using hgc
  have hn8 : 8 ≤ B.I.n := hn0
  have hf1 : 1 ≤ B.I.f := one_le_f B.I
  have hrd1 : 1 ≤ B.I.rd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn8
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf1
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b := ⟨_, rfl⟩
  have a1 : (8 : ℝ) ≤ B.I.n * B.I.f := by nlinarith
  have a2 : (8 : ℝ) ≤ B.I.n * B.I.f * B.g := by nlinarith
  have a3 : (16 : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
  have hXe : X = B.I.rd * (B.I.n * B.I.f * B.g * b) := by rw [hX]; ring
  have hX16 : 16 ≤ X := by rw [hXe]; nlinarith
  have hXrd : B.I.rd ≤ X := by rw [hXe]; nlinarith
  have hXf : 2 * B.I.f * B.I.rd ≤ X := by
    have : 2 * (B.I.f : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
    rw [hXe]; nlinarith
  have hXsq : 2 * B.I.f * B.I.rd ≤ X ^ 2 := by nlinarith
  have hVol := hV B.I p q (by first | exact hSig | exact fun v => hSig v) hqn hn8 X (by linarith) hXrd hXsq
    c B.μf (by first | exact hc | exact fun v => ⟨hc0 v, hc v⟩ | exact fun v => ⟨hc v, hc0 v⟩)
  obtain ⟨hKs, hKg0, hKsT⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg1
  obtain ⟨hcov, -⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => trivial)
  rw [Set.univ_inter] at hcov
  change ENNReal.ofReal (∏ v, c v) * _ / B.μf B.I.Kset ≤ _ at hVol
  rw [hcov] at hVol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set P : ℝ := ∏ v, c v with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => hc0 v
  have hKgT : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKsT.ne (measure_mono fun x hx => hx.1)
  set kR : ℝ := (B.μf (B.I.Kg B.g)).toReal with hkR
  have hkR0 : 0 < kR := ENNReal.toReal_pos hKg0.ne' hKgT
  have hX0 : 0 < X := by linarith
  have hg0' : (0 : ℝ) < B.g := by linarith
  have hm0 : B.μf B.I.Kset ≠ 0 := (lt_of_lt_of_le hKg0 (measure_mono fun x hx => hx.1)).ne'

  have hF : B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by
    have h1 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N) * B.μf B.I.Kset :=
      (ENNReal.div_le_iff hm0 hKsT.ne).1 hVol
    have h2 : B.μf B.I.Kset ≤ ENNReal.ofReal ((B.g : ℝ) ^ (2 * N) * kR) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hKgT, ENNReal.ofReal_pow hg0'.le,
        ENNReal.ofReal_natCast]
      exact hKs
    have h3 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤
        ENNReal.ofReal (X ^ N * ((B.g : ℝ) ^ (2 * N) * kR)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact h1.trans (by gcongr)
    rw [ENNReal.ofReal_div_of_pos hP0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hP0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← mul_assoc]
    simpa [mul_assoc] using h3

  set Kc : ℝ := Real.exp (-(N : ℝ)) / ((B.g : ℝ) ^ (2 * N) * X ^ N) * B.D * P / kR with hKc
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b,
      ENNReal.ofReal (kern B.I (phe B d) x x).re ≤ ENNReal.ofReal Kc := by
    intro x hx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
    apply ENNReal.ofReal_le_ofReal
    have hτ0 : 0 < least B.I x :=
      ((GlobalTheory.T.canonicalLatticeFiltration_size_properties B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
    have hτle : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hx.2.le
    have hk := hK Cg 8 B d p q b c x hCg le_rfl hq hH hc hx.2
    have he := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf1 hq hqn
      hrd1 hb hgR hτ0 hτle).2
    have hN' : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
    have hst : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
        √(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
      have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * √(B.I.n : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by positivity), Real.rpow_one]
      rw [this]; push_cast; ring
    rw [hN', hst] at hk
    rw [hX] at hKc
    have hA : ((2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * √(B.I.f : ℝ) *
          (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^
            (16 * q * N) *
          (6 * (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
            3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N *
          Real.exp B.I.f * (17 * √(B.I.n : ℝ) / least B.I x ^ 2) ^ (2 * N)) *
          ((B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N) ≤
          Real.exp (-(N : ℝ)) := by
      rw [show 16 * q * N = 2 * (8 * q * N) by ring]
      refine le_of_eq_of_le ?_ he
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh]
      ring
    have hD : (0 : ℝ) ≤ B.D := Nat.cast_nonneg _
    refine hk.trans ?_
    rw [hKc]
    have hpos : 0 < (B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N := by
      rw [← hX]; positivity
    gcongr
    rw [le_div_iff₀ hpos]
    exact hA
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal Kc ∂(B.I.muA B.μf) := by
        first
          | exact setLIntegral_mono measurable_const hpt
          | exact lintegral_mono_ae ((ae_restrict_iff' (by
              simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet]; exact (measurableSet_eq_fun_of_countable
                measurable_const measurable_const))).2 (Filter.Eventually.of_forall hpt))
    _ = ENNReal.ofReal Kc * B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal Kc * B.I.muA B.μf B.fund := by
        gcongr
        intro x hx
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
        exact hx.1
    _ ≤ ENNReal.ofReal Kc * ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by gcongr
    _ = ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by rw [hKc]; positivity)]
        congr 1
        rw [hKc, hN]
        push_cast
        field_simp

end GlobalTheory.DeepRegion
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepRegion_kernelDiagonal_bound : GlobalTheory.FlagMeas.AbsoluteVolume → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  first | exact @GlobalTheory.DeepRegion.deepBound | exact GlobalTheory.DeepRegion.deepBound | (intros; apply GlobalTheory.DeepRegion.deepBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.farTermsModerateRegion_of_flagBound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  first | exact @GlobalTheory.Deep.farModerate_of_farBound | exact GlobalTheory.Deep.farModerate_of_farBound | (intros; apply GlobalTheory.Deep.farModerate_of_farBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalRowsSpaceDiscreteSeriesCountStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_rowsSpace_discreteSeriesCount : GlobalTheory.DSId.DecGap → GlobalTheory.FlagMeas.AbsoluteVolume → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) := by
  first | exact @GlobalTheory.RowsFinMult.rows_finiteDimensional | exact GlobalTheory.RowsFinMult.rows_finiteDimensional | (intros; apply GlobalTheory.RowsFinMult.rows_finiteDimensional <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagRareOfNonzeroFlagBound

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGapStatement

section

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap : FormulaGap → DecGap := by
  first | exact @GlobalTheory.DecGapBound.decGap_of_formulaGap | exact GlobalTheory.DecGapBound.decGap_of_formulaGap | (intros; apply GlobalTheory.DecGapBound.decGap_of_formulaGap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductioStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountFinal

theorem countingTheorem_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hV
  have hDec : GlobalTheory.DSId.DecGap := GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType
  have hPt : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hDec
  have hAbs : GlobalTheory.FlagMeas.AbsoluteVolume := GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction hV
  have hFM : GlobalTheory.FlagMeas.FlagMeasureBound := GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV
  have hFin := GlobalTheory.T.finiteDimensional_rowsSpace_discreteSeriesCount hDec hAbs
  have hNear := GlobalTheory.NearMod.nearModerate hFM GlobalTheory.T.flag_explicit_constant_le_exp_neg_half GlobalTheory.NearElement.near_unipotent hPt
  have hFar := GlobalTheory.T.farTermsModerateRegion_of_flagBound hFM (GlobalTheory.FarTerms.farBound_of_ptBound hPt)
  have hRare := GlobalTheory.FlagRareProof.flagRare_of_nonzeroFlagBound (GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction hV)
  have hDeep := GlobalTheory.T.deepRegion_kernelDiagonal_bound hAbs (GlobalTheory.T.deepPointKernelBound_of_pointwiseBound hPt hFin)
  exact GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds hFin hFM hPt hNear hFar hRare hDeep

end GlobalTheory.CountFinal
end
end
