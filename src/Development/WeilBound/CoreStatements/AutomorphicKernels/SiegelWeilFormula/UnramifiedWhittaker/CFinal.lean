module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramifiedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramifiedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReductionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramifiedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormulaStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.LocCMain

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem trace_red_mul {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k A * red ϖ k B) = Ideal.Quotient.mk (lev ϖ k) (∑ a, ∑ c, A a c * B c a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, red, Matrix.map_apply, map_sum, map_mul]

theorem psiLev_holds : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.PsiLev
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT k X hX
  rw [trace_red_mul]
  show _ = PositivityTheory.SiegelWeilFormula.Gunr.psiF ψv ϖ _ k _
  unfold PositivityTheory.SiegelWeilFormula.Gunr.psiF PositivityTheory.PfSWUS.Loc.trPair
  congr 1
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.hermOf, PositivityTheory.SiegelWeilFormula.Gunr.GoodLoc.hermLev, PositivityTheory.SiegelWeilFormula.Gunr.matS,
    Matrix.map_apply, Matrix.of_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
  rw [one_div, map_inv₀, map_ofNat]
  ring

end GlobalTheory.CompanionTheory.GunrLev

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.character_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | exact GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | (intros; apply GlobalTheory.CompanionTheory.GunrLev.psiLev_holds <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.multiplicity_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | exact GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula

section

@[expose] public section

noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.SiegLoc

namespace GlobalTheory.CompanionTheory.GunrNu

theorem card_range_pow {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) (d : R) (hd : σ d = d) :
    ∃ e : ℕ, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) =
      (q ^ 2) ^ e := by
  rcases Scaled.fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    have hr : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
      ext z
      simp [hz]
    exact ⟨0, by rw [hr]; simp⟩
  · exact ⟨e, by
      rw [Scaled.card_range_mul hR.reg (hR.fixLocal c hc hc1) e a₀,
        GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR e, pow_mul]⟩

theorem nuPow : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  intro R _ σ ϖ q ε hR n k B hB
  obtain ⟨h, hh, rfl⟩ := hB
  have hq := hR.one_lt
  have hfin : Finite (R ⧸ lev ϖ k) := Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k]
    exact pow_ne_zero _ (by omega))
  let _ : Fintype (R ⧸ lev ϖ k) := Fintype.ofFinite _
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  choose eI hcard using fun i => card_range_pow hR k (d i) (hd i)
  have hnu : nuAt ϖ (red ϖ k h) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd,
      Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow (Nat.one_lt_pow (by norm_num) hq)]

end GlobalTheory.CompanionTheory.GunrNu

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter Topology

variable {α E : Type*} [NormedAddCommGroup E]

theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramifiedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.tsum_exhaustion_unramified : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CFinal

section

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem unrPoly : PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := GlobalTheory.T.unramified_formula_polynomial_gen GlobalTheory.T.unramified_local_formula

theorem locC : LocC :=
  locC_of_steps unrPoly GlobalTheory.T.coset_integral_unramified GlobalTheory.T.tsum_exhaustion_unramified GlobalTheory.T.multiplicity_power_formula GlobalTheory.T.multiplicity_bound_unramified GlobalTheory.T.level_characters_unramified GlobalTheory.T.integral_hermitian_volume_one GlobalTheory.T.level_joint_reduction GlobalTheory.T.multiplicity_level_formula GlobalTheory.T.character_level_formula GlobalTheory.T.level_exhaustion GlobalTheory.T.class_level_formula GlobalTheory.T.integral_hermitian_invariance GlobalTheory.T.coset_measure_formula

end PositivityTheory.SiegelWeilFormula.Gunr
end
end
