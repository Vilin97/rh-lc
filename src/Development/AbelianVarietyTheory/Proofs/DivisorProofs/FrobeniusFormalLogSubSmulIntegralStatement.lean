module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDpStatement
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
public import Mathlib.RingTheory.MvPowerSeries.Expand
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubstMapCongrPowModP

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FrobCong

theorem frobenius_congr (p : ℕ) [hpf : Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B)
    (hσ : ∀ b, (p : B) ∣ σB b - b ^ p) (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ) :
    (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  have hp : p ≠ 0 := hpf.out.ne_zero
  set I : Ideal B := Ideal.span {(p : B)} with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g)
      = expand p hp (map σB g) := by
    rw [expand, substAlgHom_apply]
  rw [hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ,
    ← coeff_map, map_sub, map_pow, map_expand, map_map]
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hs
  · exact Subsingleton.elim _ _
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    have h1 : π (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rwa [map_natCast] at h1
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out
  have hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubstMapCongrPowModPStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B), (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ), (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  first | exact @GlobalTheory.FrobCong.frobenius_congr | exact GlobalTheory.FrobCong.frobenius_congr | (intros; apply GlobalTheory.FrobCong.frobenius_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegral

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegralStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.frobenius_formalLog_sub_smul_integral : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) → (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 → In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) - (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.in_frob_formalLog_sub_smul | exact GlobalTheory.QLog.in_frob_formalLog_sub_smul | (intros; apply GlobalTheory.QLog.in_frob_formalLog_sub_smul <;> assumption)
end
end
