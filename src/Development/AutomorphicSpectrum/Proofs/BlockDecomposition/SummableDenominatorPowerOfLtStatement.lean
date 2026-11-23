module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.CompletelyRegular
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU

variable {E : Type} [Field E] [NumberField E] {m : ℕ}

theorem fibre_bound (c : Matrix (Fin m) (Fin m) E) (b : (Fin m → E) ⧸ lam c) :
    Finite {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ∧
      Nat.card {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ≤ delta c := by
  obtain ⟨hne, hidx⟩ := GlobalTheory.T.delta_eq_lattice_index E m c
  set H := (intVec E m).toAddSubgroup with hH
  set Kg := (lam c).toAddSubgroup with hK
  have hidx' : delta c = (H.addSubgroupOf Kg).index := hidx
  have hcard : Nat.card (Kg ⧸ H.addSubgroupOf Kg) = delta c := by
    rw [hidx']; rfl
  haveI : Finite (Kg ⧸ H.addSubgroupOf Kg) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have hw : (Submodule.Quotient.mk (Quotient.out b) : (Fin m → E) ⧸ lam c) = b :=
    Quotient.out_eq' b
  have hmem : ∀ a : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b},
      Quotient.out a.1 - Quotient.out b ∈ Kg := by
    intro a
    have : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ lam c) =
        Submodule.Quotient.mk (Quotient.out b) := a.2.trans hw.symm
    exact (Submodule.Quotient.eq _).1 this
  let φ : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} →
      Kg ⧸ H.addSubgroupOf Kg := fun a => QuotientAddGroup.mk ⟨_, hmem a⟩
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := QuotientAddGroup.eq.1 h
    have h2 : -(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b) ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 h1
    have h3 : Quotient.out a.1 - Quotient.out a'.1 ∈ intVec E m := by
      have h4 := neg_mem h2
      have h5 : -(-(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b)) =
          Quotient.out a.1 - Quotient.out a'.1 := by abel
      rw [h5] at h4
      exact h4
    apply Subtype.ext
    have h6 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) =
        Submodule.Quotient.mk (Quotient.out a'.1) := (Submodule.Quotient.eq _).2 h3
    have e1 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) = a.1 :=
      Quotient.out_eq' _
    have e2 : (Submodule.Quotient.mk (Quotient.out a'.1) : (Fin m → E) ⧸ intVec E m) = a'.1 :=
      Quotient.out_eq' _
    rw [← e1, ← e2, h6]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem sum_tor : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  intro E _ _ m c r hr
  obtain ⟨hs, hle⟩ := GlobalTheory.T.torsion_norm_zeta_bound E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) r hr
  have hg : ∀ x : (Fin m → E) ⧸ lam c,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
        (-((m : ℝ) + r)) := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le ((Fin m → E) ⧸ intVec E m) ((Fin m → E) ⧸ lam c)
    (fun U => Submodule.Quotient.mk (Quotient.out U)) (delta c) (fibre_bound c)
    (fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
      (-((m : ℝ) + r))) hg hs
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDeltaStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.torsion_sum_zeta_bound_delta : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLt

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := GlobalTheory.T.delta_block_quotient_injection F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact Summable.of_finite
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLtStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow <;> assumption)
end
end
