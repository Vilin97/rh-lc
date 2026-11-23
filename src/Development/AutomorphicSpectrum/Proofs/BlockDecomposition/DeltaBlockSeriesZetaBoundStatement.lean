module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.ideal_principal_element_norm_bound : ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBoundStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_block_series_zeta_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le <;> assumption)
end
end
