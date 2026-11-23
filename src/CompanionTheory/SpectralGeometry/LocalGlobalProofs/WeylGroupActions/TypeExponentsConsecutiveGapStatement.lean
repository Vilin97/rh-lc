module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.FrameExists2

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.CapelliParamsDiffInt

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegers

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapInt

theorem type_param_diff_int : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  intro Wq _ _ _ k r z π u hz hT hty i hi j hj
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Bs, hB⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists hz hT
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : Qr.IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear Wq (n + 1) r (n + 1) z π Bs hR hB
  have hc : ∀ w v, qdet (Qr.EB π Bs) w v =
      Qr.cpol (fun a : Fin (n + 1) => (u ((a : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) w • v := by
    intro w v
    rw [← hq w v, hcap Bs hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold Qr.cpol
    refine Finset.prod_congr rfl (fun a _ => ?_)
    ring
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.GapLie.capelli_params_diff_int Wq (n + 1) (Qr.EB π Bs) _ hgl hc
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  refine ⟨N, ?_⟩
  have e1 : i - 1 + 1 = i := by omega
  have e2 : j - 1 + 1 = j := by omega
  simp only [e1, e2] at hN
  have h : ((u i : ℝ) : ℂ) - (u j : ℂ) = (N : ℂ) := by linear_combination hN
  exact_mod_cast h

end GlobalTheory.CompanionTheory.GapInt
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegersStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.type_exponents_differ_by_integers : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | exact GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | (intros; apply GlobalTheory.CompanionTheory.GapInt.type_param_diff_int <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGap

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.TypeGaps

theorem gap_eq_nat_add_one :
    ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ),
      inWb k r z → 0 < Tz k r z → IsType k r z π u →
      (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) →
      ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  intro Wq _ _ _ k r z π u hz hT hty hdec i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨N, hN⟩ := GlobalTheory.T.type_exponents_differ_by_integers Wq k r z π u hz hT hty i
    (Finset.mem_Icc.2 ⟨hi.1, by omega⟩) (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h1 := hdec i (Finset.mem_Ico.2 ⟨hi.1, by omega⟩)
  have h2 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have h3 : (1 : ℤ) ≤ N := by exact_mod_cast h2
  refine ⟨(N - 1).toNat, ?_⟩
  have h4 : (((N - 1).toNat : ℕ) : ℤ) = N - 1 := Int.toNat_of_nonneg (by omega)
  have h5 : (((N - 1).toNat : ℕ) : ℝ) = (N : ℝ) - 1 := by exact_mod_cast h4
  rw [hN, h5]
  ring

end GlobalTheory.CompanionTheory.TypeGaps
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGapStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.type_exponents_consecutive_gap : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) → ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | exact GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | (intros; apply GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one <;> assumption)
end
end
