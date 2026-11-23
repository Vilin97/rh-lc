module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimET
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Formalism.HermitianCurvature.StatementLE
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroLimitOfXiExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsAlt

section

@[expose] public section

namespace GlobalTheory.JetConstSq

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (b Λ : ℝ) (r n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → 2 * (3 * b) ^ (2 * n₀) * (1 * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  intro C₃ CΛ C₀ C₂ h3 hΛ h0 h2
  refine ⟨40 + CΛ + C₂ + 2 * C₃ * (C₀ + 9), ?_⟩
  intro b Λ r n₀ p₀ hb hΛ1 hΛb hn hp
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hnR : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hq : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀ := by push_cast; ring
  have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [hm] at hΛb
  rw [hm, hq]
  have hs : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith

  have hC2 : C₂ ≤ b ^ C₂ := by
    have h1 : (1 : ℝ) ≤ Real.log b := by
      rw [Real.le_log_iff_exp_le hb0]
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.rpow_def_of_pos hb0]
    have h4 : C₂ ≤ Real.log b * C₂ := by nlinarith
    have := Real.add_one_le_exp (Real.log b * C₂)
    linarith
  have e1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have e2 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ)) := by
    have : (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    refine this.trans (le_of_eq ?_)
    rw [show (4 * (n₀ : ℝ)) = ((4 * n₀ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have e3 : 1 * (C₂ * Λ ^ 2) ^ (r + 1) ≤
      b ^ ((C₂ + 2 * (CΛ * (2 * ((r : ℝ) + 1)))) * ((r : ℝ) + 1)) := by
    rw [one_mul, Real.rpow_mul hb0.le, ← hr, Real.rpow_natCast]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Real.rpow_add hb0, mul_comm (2 : ℝ) (CΛ * _), Real.rpow_mul hb0.le, Real.rpow_two, hr]
    exact mul_le_mul hC2 (pow_le_pow_left₀ (by linarith) hΛb 2) (by positivity) (by positivity)
  generalize ((r : ℝ) + 1) = s at *
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  calc _ ≤ b ^ (1 : ℝ) * b ^ (4 * (n₀ : ℝ)) * b ^ ((C₂ + 2 * (CΛ * (2 * s))) * s) *
        b ^ (2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        gcongr
    _ = b ^ (1 + 4 * (n₀ : ℝ) + (C₂ + 2 * (CΛ * (2 * s))) * s +
        2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have a1 : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
        have a2 : C₂ * s ≤ C₂ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ h2.le; nlinarith
        have a3 : CΛ * (4 * s ^ 2) ≤ CΛ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ hΛ; nlinarith
        have a4 : 2 * (p₀ : ℝ) + n₀ ≤ (C₀ + 9) * (2 * s) ^ 2 := by
          have : 0 ≤ C₀ * s ^ 2 := by positivity
          nlinarith
        have a5 : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤
            2 * C₃ * (2 * s) ^ 2 * ((C₀ + 9) * (2 * s) ^ 2) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
        nlinarith

end GlobalTheory.JetConstSq
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeOfProdLinearLe

section

section

namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

open MvPolynomial

end Formalism.FourierDecayAlt.P.LEx2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellJetBoundShiftedTypePlace

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundShifted

open Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem bigCellJetBound_shiftedTypePlace {P : M.Par} {Wp Wq Wq' : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {up up' : ℕ → ℝ}
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 0 < Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew q (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 q F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun c => ?_
  rw [← ENNReal.ofReal_mul hT0]
  refine ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))
  ring

end GlobalTheory.JetBoundShifted

namespace GlobalTheory.JetBoundShifted

open MeasureTheory
open scoped ENNReal

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp)) (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b Λ : ℝ) (n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → TBB.TTp pp = TBB.TTp p → TBB.TTp pm = TBB.TTp p → NormAtSh p pp pm f Fp Fm b n₀ p₀ → TBB.PtBound pp Fp (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.PtBound pm Fm (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetConstSq.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ n₀ p₀ hb hΛ hΛb
    hn₀ hp₀ htp htm hNorm hPp hPm hReg γ hγ hG
  have hGp : 0 < TBB.Gp pp γ := by rw [gp_eq p pp htp]; exact hG
  have hGm : 0 < TBB.Gp pm γ := by rw [gp_eq p pm htm]; exact hG
  have hK := hC₄ b Λ P.r n₀ p₀ hb hΛ hΛb hn₀ hp₀
  set G := TBB.Gp p γ with hGdef
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < TBB.Tq p := p.T.base.T'_pos
  set c : ℝ := 1 * (C₂ * Λ ^ 2) ^ (P.r + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set T : ℝ := (TBB.Tq p)⁻¹ ^ n₀ with hTdef
  have hT0' : 0 ≤ T := by positivity
  set B3 : ℝ := b ^ (2 * C₃ * m ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) with hB3
  have hB30 : 0 ≤ B3 := by positivity
  set A : ℝ := (3 * b) ^ (2 * n₀) * (TBB.Tq p / G) ^ n₀ * G⁻¹ ^ (2 * p₀) with hA
  have hA0 : 0 ≤ A := by positivity
  set J := TBB.jN2 p f
  have hReg' : TBB.bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) ≤ ENNReal.ofReal B3 * J := hReg _ le_rfl
  have hEp : ENNReal.ofReal (TBB.Ew pp (fun _ => 1) Fp (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPp γ hγ hGp).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pp f Fp n₀ p₀ hT0 fun c => hNorm.2.1 c).trans (by gcongr)
  have hEm : ENNReal.ofReal (TBB.Ew pm (fun _ => 1) Fm (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPm γ hγ hGm).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pm f Fm n₀ p₀ hT0 fun c => hNorm.2.2 c).trans (by gcongr)
  set X := ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J))
  have hE : ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤ ENNReal.ofReal A * (2 * X) := by
    refine (ENNReal.ofReal_le_ofReal (hNorm.1 γ hγ hG)).trans ?_
    rw [ENNReal.ofReal_mul hA0]
    gcongr
    refine ENNReal.ofReal_add_le.trans ?_
    rw [two_mul]; exact add_le_add hEp hEm
  refine hE.trans ?_
  clear_value A c T B3 J G m
  have hX : ENNReal.ofReal A * (2 * X) = ENNReal.ofReal (A * 2 * c * T * B3) * J := by
    simp only [X]
    rw [show A * 2 * c * T * B3 = A * (2 * (c * (T * B3))) by ring, ENNReal.ofReal_mul hA0,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hT0', ENNReal.ofReal_ofNat]
    ring
  rw [hX]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
  have hGne : G ≠ 0 := hG.ne'
  have heq : A * 2 * c * T * B3 = (2 * (3 * b) ^ (2 * n₀) * c * B3) * G⁻¹ ^ (2 * p₀ + n₀) := by
    simp only [hA, hTdef]
    rw [pow_add, div_eq_mul_inv]
    have : (TBB.Tq p * G⁻¹) ^ n₀ * (TBB.Tq p)⁻¹ ^ n₀ = G⁻¹ ^ n₀ := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * (3 * b) ^ (2 * n₀) * G⁻¹ ^ (2 * p₀) * c * B3) * this
  rw [heq]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

end GlobalTheory.JetBoundShifted
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetBoundEqualTypesThreePlacesOfXiIntegrable

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundEqualTypesReg

theorem of_compact : P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₂, Cc, hC₂, hPt⟩ := GlobalTheory.PointwiseBoundDecay.main hA Cb
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetBoundShifted.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, Cc, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d χ nnp nnm
    Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm hth
    hAms hReg hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := normaliser_across_places P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hzp hzp' hzm hzm' hAms
  have hdp := shifted_decay P Wp Wq Wqp up up' pp f Ap A₀ d p₀ hfA hAp
  have hdm := shifted_decay P Wp Wq Wqm um um' pm f Am A₀ d p₀ hfA hAm
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ _ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hdp hth hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ _ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hdm hth hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ n₀ p₀ hb hΛ hΛb hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ :=
  fun _ => of_compact

end GlobalTheory.JetBoundEqualTypesReg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetBoundEqualTypesThreePlacesOfXiIntegrableStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.JetBoundEqualTypesReg.main | exact GlobalTheory.JetBoundEqualTypesReg.main | (intros; apply GlobalTheory.JetBoundEqualTypesReg.main <;> assumption)
end
end
