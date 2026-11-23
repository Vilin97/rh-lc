module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSumStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyReal

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.BalancedUnits

open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem sum_mult_log_sub {K : Type} [Field K] [NumberField K] (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) = 0 := by
  have h1 : ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (normAtPlace w x) =
      Real.log (mixedEmbedding.norm x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have h2 : ∑ w : InfinitePlace K, (mult w : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast sum_mult_eq
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp_rw [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, h2]
  field_simp
  ring

theorem exists_unit_log_bound (K : Type) [Field K] [NumberField K] : ∃ M : ℝ, 0 ≤ M ∧
    ∀ b : K, b ≠ 0 → ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log (w (((ε : 𝓞 K) : K) * b)) -
        Real.log (mixedEmbedding.norm (mixedEmbedding K (((ε : 𝓞 K) : K) * b))) *
          (Module.finrank ℚ K : ℝ)⁻¹| ≤ M := by
  classical
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))).subset_closedBall 0
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * |R|, by positivity, ?_⟩
  intro b hb
  have hx : mixedEmbedding.norm (mixedEmbedding K b) ≠ 0 := by
    rw [norm_eq_norm]; simpa using hb
  obtain ⟨ε, hε⟩ := fundamentalCone.exists_unit_smul_mem hx
  refine ⟨ε, ?_⟩
  have hxy : ε • mixedEmbedding K b = mixedEmbedding K (((ε : 𝓞 K) : K) * b) := by
    rw [unitSMul_smul, map_mul]
  rw [hxy] at hε
  set y : K := ((ε : 𝓞 K) : K) * b with hy_def
  set X := mixedEmbedding K y
  set L := Real.log (mixedEmbedding.norm X) * (Module.finrank ℚ K : ℝ)⁻¹
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(mult w.val : ℝ) * (Real.log (normAtPlace w.val X) - L)| ≤ |R| := by
    intro w
    have h0 := hR hε.1
    rw [mem_closedBall_zero_iff] at h0
    have h2 := (norm_le_pi_norm (logMap X) w).trans h0
    rw [logMap_apply, Real.norm_eq_abs] at h2
    exact h2.trans (le_abs_self R)
  have hmul : ∀ w : InfinitePlace K,
      |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)| ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have hs := sum_mult_log_sub X hε.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      rw [eq_neg_of_add_eq_zero_left hs, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ w ∈ Finset.univ.erase w₀, |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)|
          ≤ ∑ _w ∈ Finset.univ.erase w₀, |R| := Finset.sum_le_sum fun w hw =>
            hlog ⟨w, Finset.ne_of_mem_erase hw⟩
        _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (hlog ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg R) hcard)
  intro w
  have h := hmul w
  rw [abs_mul, normAtPlace_apply] at h
  refine le_trans ?_ h
  rw [abs_of_pos (by exact_mod_cast mult_pos : (0:ℝ) < mult w)]
  exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult

theorem balanced_unit_multiple (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F,
      |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  obtain ⟨M, hM0, hM⟩ := exists_unit_log_bound F
  refine ⟨Real.exp (2 * M), Real.one_le_exp (by positivity), ?_⟩
  intro b hb
  obtain ⟨ε, hε⟩ := hM b hb
  refine ⟨ε, ?_⟩
  set y : F := ((ε : 𝓞 F) : F) * b with hy_def
  have hy : y ≠ 0 := mul_ne_zero (by simp) hb
  have hw : ∀ τ : Emb F, InfinitePlace.mk (Complex.ofRealHom.comp τ) y = |τ y| := by
    intro τ
    rw [InfinitePlace.apply]
    simp
  have hpos : ∀ τ : Emb F, 0 < |τ y| := fun τ => abs_pos.mpr ((map_ne_zero τ).mpr hy)
  intro τ τ'
  have h1 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ))
  have h2 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ'))
  rw [hw] at h1 h2
  have key : Real.log |τ y| ≤ 2 * M + Real.log |τ' y| := by
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    linarith
  calc |τ y| = Real.exp (Real.log |τ y|) := (Real.exp_log (hpos τ)).symm
    _ ≤ Real.exp (2 * M + Real.log |τ' y|) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * M) * |τ' y| := by rw [Real.exp_add, Real.exp_log (hpos τ')]

end GlobalTheory.BalancedUnits
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyRealStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.exists_balanced_unit_multiple_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 1 ≤ C ∧
    ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F, |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  first | exact @GlobalTheory.BalancedUnits.balanced_unit_multiple | exact GlobalTheory.BalancedUnits.balanced_unit_multiple | (intros; apply GlobalTheory.BalancedUnits.balanced_unit_multiple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnit

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoUnit

theorem phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]
  ring

theorem abs_mul_inv_sq {l : ℝ} (hl : l ≠ 0) :
    ((|l| : ℝ) : ℂ) * (l : ℂ)⁻¹ ^ 2 = ((|l| : ℝ) : ℂ)⁻¹ := by
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hl
  have h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [inv_pow, h2]; field_simp

theorem hTrans_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (ν y : ℝ) :
    hTrans σ ν (l * y) = ((|l| : ℝ) : ℂ) ^ (-1 - 2 * σ) * hTrans σ (l * ν) y := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l
  unfold hTrans
  rw [← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]
  have habs : |l⁻¹| = |l|⁻¹ := abs_inv l
  have hpos : 0 < |l| := abs_pos.2 hl
  have e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) =
      |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) := by
    rw [key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [e1]
  have e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) =
      ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t
    rw [show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring,
      phi_smul σ hl]
    push_cast; ring_nf
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    abs_mul_inv_sq hl]
  congr 1
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem prod_abs_unit_cpow {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ε : (𝓞 F)ˣ) (s : ℂ) :
    ∏ τ : Emb F, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = 1 := by
  have hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s =
      ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
  rw [hprod]
  have h := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)
  rw [← Complex.ofReal_prod] at h
  have hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
    have := Units.norm F ε
    exact_mod_cast this
  rw [← h, hn, Complex.ofReal_one, Complex.one_cpow]

theorem fTerm_unit_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F)
    (ε : (𝓞 F)ˣ) :
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  have hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0 := fun τ h => by
    have hu : ((ε : 𝓞 F) : F) ≠ 0 := by
      intro h0; have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact hu ((map_eq_zero τ).1 h)
  unfold fTerm
  have e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) =
      ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ b * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ (((ε : 𝓞 F) : F) * ν)) (τ b * (z τ).im)) := by
    intro τ
    rw [map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]
    rw [show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem fTerm_unit_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) :=
  fun _ _ _ _ σ z b ν ε => fTerm_unit_mul σ z b ν ε

end GlobalTheory.HeckeTwoUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnitStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeEisensteinFourierTerm_move_unit : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  first | exact @GlobalTheory.HeckeTwoUnit.fTerm_unit_move | exact GlobalTheory.HeckeTwoUnit.fTerm_unit_move | (intros; apply GlobalTheory.HeckeTwoUnit.fTerm_unit_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fTerm_deriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  intro F _ _ _ 𝔞 𝔟 K hK hKH L hL hLU n
  obtain ⟨m, hm⟩ := GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact F K hK hKH L hL hLU n
  obtain ⟨C₀, -, hC₀⟩ := GlobalTheory.T.exists_balanced_unit_multiple_totallyReal F
  obtain ⟨N, hN⟩ := GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum F 𝔞 𝔟 C₀ m
  obtain ⟨C, hC⟩ := hm N
  choose ε hε using fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => hC₀ c.out.1 c.out.2.2
  refine ⟨fun p => C * ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N, (hN ε hε).mul_left C, ?_⟩
  rintro ⟨c, ν⟩ σ hσ z hz
  have hee : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
  have hfun : (fun z : Emb F → ℂ => fTerm σ z c.out.1 ν.1) =
      fun z => fTerm σ z (((ε c : 𝓞 F) : F) * c.out.1) (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) := by
    funext z
    have hb : c.out.1 = ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((ε c : 𝓞 F) : F) * c.out.1) := by
      rw [← mul_assoc, hee, one_mul]
    conv_lhs => rw [hb]
    exact GlobalTheory.T.heckeEisensteinFourierTerm_move_unit F σ z _ _ (ε c)⁻¹
  have hb0 : ((ε c : 𝓞 F) : F) * c.out.1 ≠ 0 := mul_ne_zero (right_ne_zero_of_mul_eq_one hee) c.out.2.2
  have hν0 : ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hee) ν.2.2
  dsimp only
  rw [hfun]
  refine (hC σ hσ z hz _ _ hb0 hν0).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrArg τ hee
  rw [map_mul, map_one] at h1
  have h2 : τ (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) * τ (((ε c : 𝓞 F) : F) * c.out.1) = τ ν.1 * τ c.out.1 := by
    rw [map_mul, map_mul]; linear_combination (τ ν.1 * τ c.out.1) * h1
  rw [h2]

end GlobalTheory.HeckeTwo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBoundStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | exact GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | (intros; apply GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound <;> assumption)
end
end
