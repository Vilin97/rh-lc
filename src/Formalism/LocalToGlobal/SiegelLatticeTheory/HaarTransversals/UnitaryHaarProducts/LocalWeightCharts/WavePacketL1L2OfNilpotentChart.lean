module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.PsiGenNorm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AKindR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ANonzeroOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DecayR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalUnimodularConjInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationUnitary
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SubgroupHypothesisHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfHypotheses

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.L2SGWfEqOne

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk

section Scale

variable {k r : ℕ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

lemma rconv_smul (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) : rconv μ e (fun g => cc • A g) x = cc • rconv μ e A x := by
  unfold rconv
  simp_rw [smul_comm (e _) cc]
  exact integral_smul cc _

lemma integrable_smul_fun (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) (h : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • A (x * Matrix.of g)) μ) :
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • (fun y => cc • A y) (x * Matrix.of g)) μ := by
  simp_rw [smul_comm (e _) cc]
  exact h.smul cc

lemma l2SG_const_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) :
    l2SG ν (fun g => cc • A g) = (‖cc‖₊ : ℝ≥0∞) ^ 2 * l2SG ν A := by
  unfold l2SG
  rw [← lintegral_const_mul' _ _ (by simp)]
  congr 1
  funext x
  rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]

lemma l2SG_Wf_eq_one (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (h0 : l2SG ν A ≠ 0)
    (h1 : l2SG ν A < ⊤) : l2SG ν (Wf ν A) = 1 := by
  have hW : Wf ν A = fun g => (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) • A g := by
    funext g; unfold Wf; congr 1; push_cast; rfl
  rw [hW, l2SG_const_smul]
  set t := (l2SG ν A).toReal with ht_def
  have ht : 0 < t := ENNReal.toReal_pos h0 h1.ne
  have hA : l2SG ν A = ENNReal.ofReal t := (ENNReal.ofReal_toReal h1.ne).symm
  have hn : (‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal t⁻¹ := by
    rw [ENNReal.ofReal, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]
  rw [hn, hA, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]

lemma lint_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (h : ∫⁻ x, ‖A (Matrix.of x)‖ₑ * f x ∂ν < ⊤) :
    ∫⁻ x, ‖(fun g => cc • A g) (Matrix.of x)‖ₑ * f x ∂ν < ⊤ := by
  simp_rw [enorm_smul, mul_assoc]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top h

end Scale

def WlocShape : Prop :=
  BesselNVGap → CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp, (ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧ IsSPsiEquiv z (psiGen k r z c) π W ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν W = 1 ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤ ∧
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧
      Ω ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • W (x * Matrix.of g)) μG ∧
        rconv μG α W x = W x) ∧
  ∃ (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (cc : ℂ) (x₀ : Mat k r) (ξ : Vp),
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∀ x, W x = cc • B0 z c σ π μW μN (σ x₀ w) ξ (σ x w)

theorem scWlocShape_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocShape := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨μW, μN, hW, hN, hWf, hNc⟩ := hWN k r z hS.2.2.1 hS.2.2.2.1
  have hyp : Hyp k r z c u v b σ π w μG μS ν μW μN :=
    ⟨hS, hσ, hπ, hw, hG, hSμ, hQ, hW, hN, hWf, hNc⟩
  obtain ⟨x₀, hx₀, ξ, hne⟩ := hNz hBNV k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW
  have hL' := hL k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  set A := Af z c σ π μW μN w x₀ ξ with hA_def
  set cc : ℂ := (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) with hcc
  have hW' : Wf ν A = fun g => cc • A g := by
    funext g; unfold Wf; congr 1; rw [hcc]; push_cast; rfl
  refine ⟨Wf ν A, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, μW, μN, cc, x₀, ξ, hW, hN, hx₀, fun x => by rw [hW']; rfl⟩
  · rw [hW']
    exact (hC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ).const_smul cc
  · intro h hh m hm g hg
    rw [hW']
    have := hEq k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
    change cc • Af z c σ π μW μN w x₀ ξ (h * m * g) =
      psiGen k r z c m • (π h) (cc • Af z c σ π μW μN w x₀ ξ g)
    rw [this, smul_comm cc (psiGen k r z c m), map_smul]
  · intro x hx
    obtain ⟨hi, he⟩ := hK k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩
  · rw [hW']
    have := lint_smul ν A cc (fun _ => 1) (by simpa using hL'.1)
    simpa using this
  · exact l2SG_Wf_eq_one ν A hne hL'.2
  · rw [hW']
    exact lint_smul ν A cc _ (hWt k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ)
  · obtain ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, hα⟩ :=
      hRp k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
    refine ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, fun x hx => ?_⟩
    obtain ⟨hi, he⟩ := hα x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩

theorem scWlocExists_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocExists := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨W, hWc, _⟩ := scWlocShape_of hWN hEq hC hK hRp hL hWt hNz hR hBNV hCW k r z c u v b hS H σ hσ
    Vp π hπ w hw μG μS ν hG hSμ hQ
  exact ⟨W, hWc⟩

end WlocSk
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHaarUnique

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.MainNotions.S
open scoped ENNReal

namespace WlocSk

theorem nilradical_haar_unique : NUniq := by
  intro k r μ μ' hμ hμ'
  obtain ⟨c, hc0, hct, hc⟩ := HM.n_unique μ hμ
  obtain ⟨c', hc0', hct', hc'⟩ := HM.n_unique μ' hμ'
  refine ⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩
  rw [hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']

end WlocSk
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SigmaDecomposition

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

lemma cay_inv_mul {P : Mat k r} (hP : IsUnit P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mul_inv {P : Mat k r} (hP : IsUnit P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mem {P : Mat k r} (hP : IsCayley k r ε P) {g : Mat k r} (hg : g ∈ Gr k r) :
    P * g * P⁻¹ ∈ UJset ε := by
  have h2 := cay_mul_inv hP.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [← hP.2] at hg'
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hg']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2]; simp

lemma cay_back {P : Mat k r} (hP : IsUnit P) (g : Mat k r) : P⁻¹ * (P * g * P⁻¹) * P = g := by
  have h1 := cay_inv_mul hP
  have h2 := cay_mul_inv hP
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

end Cayley

theorem sigma_decomposition : SigmaG := by
  intro k r ε lam H _ _ σ hσ
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  have hPu := hP.1.1
  have hσ' : ∀ g, σ g = σ (P⁻¹ * (P * g * P⁻¹) * P) := fun g => by rw [cay_back hPu]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := h1
    simp only [Matrix.mul_one, cay_inv_mul hPu] at this
    exact this
  · intro a ha b hb
    have hab : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
            rw [cay_inv_mul hPu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = P * a * P⁻¹ * (P * b * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hσ' (a * b), hab]
    have := hmul _ (cay_mem hP.1 ha) _ (cay_mem hP.1 hb)
    simp only at this
    rw [this, cay_back hPu, cay_back hPu]
  · intro g hg v
    rw [hσ' g]
    exact hiso _ (cay_mem hP.1 hg) v
  · intro v
    have hc : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hcont v).comp hc.continuousOn (fun g hg => cay_mem hP.1 hg)
    refine this.congr (fun g _ => ?_)
    simp only [Function.comp]
    rw [cay_back hPu]

end WlocSk
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnipotentRightInvariance

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace WlocSk.WRI

open Formalism.QuantumDeterminants WlocSk.HM

variable {k r : ℕ}

theorem haar_right_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [CompactSpace G] (g : G) :
    (Measure.haar : Measure G).map (· * g) = Measure.haar := by
  set μ : Measure G := Measure.haar
  set ν : Measure G := μ.map (· * g)
  have hν : ν = Measure.haarScalarFactor ν μ • μ := Measure.isMulLeftInvariant_eq_smul ν μ
  have hmass : ν Set.univ = μ Set.univ := by
    simp only [ν]
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := by
    intro h; exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp h)
  have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have hc : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) = 1 := by
    have e := hmass
    rw [hν, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    have e2 : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) * μ Set.univ = 1 * μ Set.univ := by
      rw [one_mul]; exact e
    exact (ENNReal.mul_left_inj h0 htop).mp e2
  rw [hν]
  have : Measure.haarScalarFactor ν μ = 1 := by exact_mod_cast hc
  rw [this, one_smul]

theorem hmeas_right (U : Set (Mx k r)) (hU : ClSub U) (hc : IsCompact U) (g : Mx k r) (hg : g ∈ U) :
    (hmeas U hU).map (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) = hmeas U hU := by
  have : CompactSpace (Grp U hU) := isCompact_iff_compactSpace.mp hc
  have hvt : Measurable (Grp.vt : Grp U hU → Mt k r) := (val_cemb U hU).continuous.measurable
  have hR : Measurable (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) := by
    have : Continuous (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) :=
      Continuous.matrix_mul continuous_id continuous_const
    exact this.measurable
  unfold hmeas
  rw [Measure.map_map hR hvt]
  have : (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) ∘ (Grp.vt : Grp U hU → Mt k r) =
      (Grp.vt : Grp U hU → Mt k r) ∘ (fun a => a * Grp.mk g hg) := by
    funext a; rfl
  rw [this, ← Measure.map_map hvt (measurable_mul_const _), haar_right_compact]

end WlocSk.WRI

open WlocSk.HM WlocSk.WRI in
theorem unipotent_right_invariance : WlocSk.WRightInv := by
  intro k r z μW hz hT hH _ h hh
  obtain ⟨c, -, -, hμ⟩ := haar_unique _ (uw_clsub z) μW hH
  have hR : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of x * h) i j) :=
    Continuous.matrix_mul continuous_id continuous_const
  rw [hμ, Measure.map_smul c hR.measurable.aemeasurable,
    hmeas_right _ _ (compactW z hz hT) h hh]
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfNilpotentChart

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.SplitPrimeNormLemmas

namespace WlocSk

theorem unipotent_set_compact : PtD.UWComp := fun _ _ z hz hT => HM.compactW z hz hT

theorem nIntDecay_of_chart (hNC : NChart) : NIntDecay := nIntDecay_of (nCoordHaar_of hNC nilradical_haar_unique)

theorem aInt_of_chart (hNC : NChart) : AInt :=
  PtD.wave_packet_integrable sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aCont_of_chart (hNC : NChart) : ACont :=
  PtD.wave_packet_continuous sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aBound_of_chart (hNC : NChart) : ABound :=
  PtD.aBound_of sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aEquiv_of_charts (hNC : NChart) (hWR : WRightInv) (hNU : NUnimod) : AEquiv :=
  aEquiv_of subgroup_hypothesis_holds representation_unitary sigma_decomposition hWR hNU (aInt_of_chart hNC)

theorem wave_packet_weighted_integrable : AWeighted :=
  AQ.aWeighted_of subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate

theorem aKind_of_chart (hNC : NChart) : AKind :=
  AK.aKind_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.decay_estimate Port.schur_orthogonality_relations

theorem aReprod_of_chart (hNC : NChart) : AReprod :=
  AK.aReprod_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.reproducing_formula_holds

theorem wave_packet_l1_l2_of_nilpotent_chart (hNC : NChart) (hWR : WRightInv) : WavePacketL1L2 :=
  AQ.wave_packet_l1_l2_of_hypotheses subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate hWR nilradical_unimodular_conj_invariant
    (aBound_of_chart hNC)

theorem aNonzero_of_charts (hNC : NChart) (hWR : WRightInv) : ANonzero :=
  ANz.aNonzero_of subgroup_hypothesis_holds representation_unitary product_decomposition_holds (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant)
    (aCont_of_chart hNC)

theorem wlocExists_of_charts (hNC : NChart) (hWR : WRightInv)
    (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  scWlocExists_of haar_measure_unipotent_nilradical (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant) (aCont_of_chart hNC)
    (aKind_of_chart hNC) (aReprod_of_chart hNC) (wave_packet_l1_l2_of_nilpotent_chart hNC hWR) wave_packet_weighted_integrable
    (aNonzero_of_charts hNC hWR) hR

theorem scWlocExists_of_chart (hNC : NChart) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  wlocExists_of_charts hNC unipotent_right_invariance hR

end WlocSk
end
end
end
