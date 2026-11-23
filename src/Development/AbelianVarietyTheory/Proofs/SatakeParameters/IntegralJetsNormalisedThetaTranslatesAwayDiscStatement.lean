module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTwelveCubedEqOneOfFiveLePrime
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodModelTwoScaleOne

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc

theorem goodModelTwo_scaleOne : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[2], ∃ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W ∧
      ‖W.a₁‖ = 1 := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  obtain ⟨hsq, -, hcm⟩ := LocJets.data ha hd lam hlam hok
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨c, hc, W', ⟨e2, e3⟩, ⟨h1, h2, h3, h4, h6, hΔ⟩, ha1⟩ := hIn.modelTwo D.host.d L hsq h8 hcm ι
  have hL1 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hlat]; rfl
    obtain ⟨f2, f3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
    rw [← f2, ← f3]
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have hh := Formalism.L2.Th1.F.homogeneity L c hc
  have s2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hh.2.2.2.2.2.2.2.2.2.1
  have s3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hh.2.2.2.2.2.2.2.2.2.2
  have g2W : W'.c₄ / 12 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := e2
  have g3W : W'.c₆ / 216 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := e3
  set u : ℂ_[2] := ι c with hu
  have hu0 : u ≠ 0 := by simpa [hu] using hc

  have hW'Δ : W'.Δ = (u ^ 12)⁻¹ := by
    have hrel := W'.c_relation
    have hc4 : W'.c₄ = 12 * ((u ^ 4)⁻¹ * ι L.g₂) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s2, ← g2W]; ring
    have hc6 : W'.c₆ = 216 * ((u ^ 6)⁻¹ * ι L.g₃) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s3, ← g3W]; ring
    have hι1 : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hL1, map_one]
    rw [hc4, hc6] at hrel
    have h1728 : (1728 : ℂ_[2]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hrel]
    field_simp
    linear_combination (1728 : ℂ_[2]) * hι1
  have hun : ‖u‖ = 1 := by
    rw [hW'Δ, norm_inv, norm_pow] at hΔ
    have h12 : ‖u‖ ^ 12 = 1 := by
      have hpos : 0 < ‖u‖ ^ 12 := pow_pos (norm_pos_iff.2 hu0) _
      field_simp at hΔ; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  let C : WeierstrassCurve.VariableChange ℂ_[2] := ⟨(Units.mk0 u hu0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) = u := by simp [C]
  refine ⟨C • W', ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (C • W').c₄ / 12 = ι L.g₂
    rw [WeierstrassCurve.variableChange_c₄, hCu, mul_div_assoc, g2W, s2, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · show (C • W').c₆ / 216 = ι L.g₃
    rw [WeierstrassCurve.variableChange_c₆, hCu, mul_div_assoc, g3W, s3, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hun, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hCu]
    simp only [C, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hun, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hun,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hun, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hCu, norm_mul, norm_pow, hun, one_pow, one_mul]; exact hΔ
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact ha1

end GlobalTheory.ThLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfDisc

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.ModelThree

theorem norm_add_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K} (hlt : ‖α‖ < ‖β‖)
    (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  have hb : 0 < ‖β‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : ‖α ^ 2 - α * β‖ < ‖β ^ 2‖ := by
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
    · rw [norm_pow, norm_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    · rw [norm_mul, norm_pow, sq]; exact mul_lt_mul_of_pos_right hlt hb
  have h2 : ‖β ^ 2 + (α ^ 2 - α * β)‖ = ‖β ^ 2‖ := norm_add_of_lt h1
  have h3 : α ^ 2 - α * β + β ^ 2 = β ^ 2 + (α ^ 2 - α * β) := by ring
  rw [h3, h2, norm_pow] at hN
  have h4 : ‖β‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact ⟨(hlt.trans_le h4).le, h4⟩

theorem norm_le_one_of_disc {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K}
    (h : ‖α * β * (α - β)‖ = 1) (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  rcases lt_trichotomy ‖α‖ ‖β‖ with hlt | heq | hgt
  · exact norm_le_one_of_lt hlt hN
  · have hc : ‖α - β‖ ≤ ‖α‖ := by
      refine (norm_sub_le_max' _ _).trans ?_
      rw [heq, max_self]
    rcases hc.lt_or_eq with hc | hc
    · have h1 : ‖(α - β) ^ 2‖ < ‖α * β‖ := by
        rw [norm_pow, norm_mul, ← heq, ← sq]
        exact pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
      have h2 : ‖α * β + (α - β) ^ 2‖ = ‖α * β‖ := norm_add_of_lt h1
      have h3 : α ^ 2 - α * β + β ^ 2 = α * β + (α - β) ^ 2 := by ring
      rw [h3, h2, norm_mul, ← heq] at hN
      have h4 : ‖α‖ ≤ 1 := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨h4, heq ▸ h4⟩
    · rw [norm_mul, norm_mul, hc, ← heq] at h
      have h4 : ‖α‖ ^ 3 = 1 := by rw [← h]; ring
      have h5 : ‖α‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
      exact ⟨h5.le, (heq ▸ h5).le⟩
  · have hN' : ‖β ^ 2 - β * α + α ^ 2‖ ≤ 1 := by
      have : β ^ 2 - β * α + α ^ 2 = α ^ 2 - α * β + β ^ 2 := by ring
      rw [this]; exact hN
    exact (norm_le_one_of_lt hgt hN').symm

theorem exists_roots {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (g2 g3 : K) :
    ∃ α β : K, 16 * (α ^ 2 - α * β + β ^ 2) = 12 * g2 ∧
      64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) = 216 * g3 := by
  let f : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C g2 * Polynomial.X - Polynomial.C g3
  have hdeg : f.degree ≠ 0 := by
    have h3 : f.natDegree = 3 := by
      simp only [f]
      compute_degree!
    intro h
    have h0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h.le
    omega
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root f hdeg
  have he' : 4 * e ^ 3 - g2 * e - g3 = 0 := by simpa [f, Polynomial.IsRoot] using he
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (g2 - 3 * e ^ 2) (n := 2) (by norm_num)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨(-3 * e + s) / 2, (-3 * e - s) / 2, ?_, ?_⟩
  · field_simp
    linear_combination (48 : K) * hs
  · have e1 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he'
    rw [e1]
    field_simp
    linear_combination (-1728 * e : K) * hs

def twoTorsionModel {K : Type} [Field K] (α β : K) : WeierstrassCurve K := ⟨0, -(α + β), 0, α * β, 0⟩

theorem c₄_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₄ = 16 * (α ^ 2 - α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, twoTorsionModel]
  ring

theorem c₆_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₆ = 64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, twoTorsionModel]
  ring

theorem Δ_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).Δ = 16 * (α * β * (α - β)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, twoTorsionModel]
  ring

theorem norm_two : ‖(2 : ℂ_[3])‖ = 1 := by
  have e : (2 : ℂ_[3]) = algebraMap ℚ_[3] ℂ_[3] ((2 : ℕ) : ℚ_[3]) := by rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  norm_num

theorem exists_model (g2 g3 : ℂ_[3]) (hΔ : g2 ^ 3 - 27 * g3 ^ 2 = 1) (hj : ‖1728 * g2 ^ 3‖ ≤ 1) :
    ∃ W : WeierstrassCurve ℂ_[3], Formalism.L2.Th1.A.g₂ W = g2 ∧ Formalism.L2.Th1.A.g₃ W = g3 ∧ IntCurve W := by
  obtain ⟨α, β, h4, h6⟩ := exists_roots g2 g3
  have c4 : (twoTorsionModel α β).c₄ = 12 * g2 := by rw [c₄_model, h4]
  have c6 : (twoTorsionModel α β).c₆ = 216 * g3 := by rw [c₆_model, h6]
  have hD : (twoTorsionModel α β).Δ = 1 := by
    have hc := (twoTorsionModel α β).c_relation
    rw [c4, c6] at hc
    have : (1728 : ℂ_[3]) * (twoTorsionModel α β).Δ = 1728 * (g2 ^ 3 - 27 * g3 ^ 2) := by
      linear_combination hc
    exact (mul_left_cancel₀ (by norm_num) this).trans hΔ
  have n16 : ‖(16 : ℂ_[3])‖ = 1 := by
    have : (16 : ℂ_[3]) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, norm_two, one_pow]
  have hprod : ‖α * β * (α - β)‖ = 1 := by
    have h1 := congrArg norm hD
    rw [Δ_model, norm_mul, n16, one_mul, norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1 := by
    have e : (16 * (α ^ 2 - α * β + β ^ 2)) ^ 3 = 1728 * g2 ^ 3 := by rw [h4]; ring
    have h1 : ‖(16 * (α ^ 2 - α * β + β ^ 2)) ^ 3‖ ≤ 1 := by rw [e]; exact hj
    rw [norm_pow, norm_mul, n16, one_mul] at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨ha, hb⟩ := norm_le_one_of_disc hprod hN
  refine ⟨twoTorsionModel α β, ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂
    rw [c4]; field_simp
  · unfold Formalism.L2.Th1.A.g₃
    rw [c6]; field_simp
  · refine ⟨by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_⟩
    · simp only [twoTorsionModel, norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · simp only [twoTorsionModel, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) hb
    · rw [hD, norm_one]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_iota_le_one (ι : ℂ ≃+* ℂ_[3]) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨f, hf, hr⟩ := hx
  refine norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  have h := congrArg (ι : ℂ →+* ℂ_[3]) hr
  rw [map_zero, Polynomial.hom_eval₂] at h
  have e : (@algebraMap ℤ ℂ_[3] _ _ (Ring.toIntAlgebra ℂ_[3])) = (ι : ℂ →+* ℂ_[3]).comp (algebraMap ℤ ℂ) :=
    Subsingleton.elim _ _
  rw [e]
  exact h

theorem goodModelThree : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[3], ∃ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hL ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) L hL'
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd hok.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ D.host.d hok.1 hok.2.2.1))
  have hd8 := hok.2.2.1
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) :=
    hIn.jInt D.host.d L hok.2.2.2.prime.squarefree (by omega) hcm
  have hj' : Formalism.L2.Th1.CM.jInv L = 1728 * L.g₂ ^ 3 := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [hdisc, div_one]
  rw [hj'] at hj
  have hn := norm_iota_le_one ι hj
  have hΔ : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
    have := congrArg ι hdisc
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using this
  have hn' : ‖1728 * ι L.g₂ ^ 3‖ ≤ 1 := by
    simpa only [map_mul, map_pow, map_ofNat] using hn
  obtain ⟨W, h2, h3, hW⟩ := exists_model _ _ hΔ hn'
  exact ⟨W, ⟨h2, h3⟩, hW⟩

end GlobalTheory.ThLoc.ModelThree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDisc

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

open scoped ComplexConjugate

theorem GlobalTheory.ThLoc.jetsIntegral_three (hIn : GlobalTheory.ThLoc.Inputs) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hd : 0 < dK)
    (lam : ℂ) (hlam : lam ≠ 0) (hd3 : dK % 3 = 2) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (ι : ℂ ≃+* ℂ_[3])
    (hL : GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ dK ha hd lam hlam h Λ θ 3 ι) (W : WeierstrassCurve ℂ_[3])
    (hU : Unif 3 (cmL a₀ b₀ dK ha hd lam hlam) ι W) (hW : IntCurve W)
    {κx : Type} [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (M : ℕ) (hr : ∀ k, ‖r k‖ ≤ 1) (hM : 0 < M)
    (hpM : ¬ 3 ∣ M) (ht : ∀ k, (M : ℂ) • t k ∈ Λ) {J : Type} [Fintype J] (v : J → n → ℂ)
    (hv : ∀ j, InMul (cmL a₀ b₀ dK ha hd lam hlam) Λ (v j)) {ν : Type} [Fintype ν] (A : J → ν → ℂ_[3])
    (hA : ∀ j x, ‖A j x‖ ≤ 1) :
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)) := by
  obtain ⟨hcmok, l2, l3, l4, l5⟩ := hL
  obtain ⟨-, -, hcm⟩ := GlobalTheory.ThLoc.LocJets.data ha hd lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hd lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hd lam hlam).ω₁_mem_lattice
  have hω1 : Formalism.L2.Th1.CM.omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok 1 (Or.inl rfl)
    simpa [Formalism.L2.Th1.CM.omegaK] using this
  have hω2 : conj (Formalism.L2.Th1.CM.omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok (-1) (Or.inr rfl)
    rw [GlobalTheory.ThLoc.LocJets.conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := l5
  obtain ⟨Dm, q0, hD, hq0, hfac, hgram⟩ :=
    GlobalTheory.ThLoc.LocJets.gram_transfer a₀ b₀ c₀ dK ha hd lam hlam hcmok n h Λ g₁ hiso 3 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    Formalism.L2.Th1.GD.FrameCompose_proof ℂ_[3] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) Dm (fun i j => ι (v j i))
      (fun j k => ι (Formalism.L2.Th1.GD.hOK (cmL a₀ b₀ dK ha hd lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (Formalism.L2.Th1.G.linSub (frameM (ι : ℂ →+* ℂ_[3]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[3]) (taylorMv (Formalism.L2.Th1.H.opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := GlobalTheory.ThLoc.LocJets.fourth_power_theta a₀ b₀ c₀ dK ha hd
      lam hlam hcmok n h Λ l2 l3 θ l4 3 ι g₁ ε hiso hidx hidx' hε hten (t k) M hM hpM (ht k)
    have hj := hIn.jetsThree dK _ hcmok.2.2.1 hd3 hcm ι W hU hW (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs'
    rw [← he] at hj
    exact GlobalTheory.ThLoc.LocJets.jets_linear ℂ_[3] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[3]) v A) Cm hCm hfacC
  exact GlobalTheory.ThLoc.LocJets.jets_comb r _ hr key

theorem GlobalTheory.ThLoc.jetsIntegral_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat n _ _ h Λ θ p _ ι hL hpd h3 κx _ r t M hr hM hpM ht
    J _ v hv ν _ A hA
  have hpr : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    obtain ⟨W, hU, hW, ha1⟩ := GlobalTheory.ThLoc.goodModelTwo_scaleOne hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact (hIn.jetsTwo a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 ι W hU hW ha1 l5 κx r t M hr hM hpM ht
      J v hv ν A hA).1
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨W, hU, hW⟩ := GlobalTheory.ThLoc.ModelThree.goodModelThree hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact GlobalTheory.ThLoc.jetsIntegral_three hIn ha hd lam hlam (h3 rfl) h Λ θ ι hL W hU hW r t M hr hM hpM ht v hv A hA
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hW := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat p h5 ι
  have hnd : ¬ p ∣ D.host.d := fun hdv => hpd ((Nat.prime_dvd_prime_iff_eq hpr l1.2.2.2).1 hdv)
  exact (hIn.jetsOdd a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 p hp2 hnd ι hW l5 κx r t M hr hM hpM ht
    J v hv ν A hA).1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDiscStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  first | exact @GlobalTheory.ThLoc.jetsIntegral_away_disc | exact GlobalTheory.ThLoc.jetsIntegral_away_disc | (intros; apply GlobalTheory.ThLoc.jetsIntegral_away_disc <;> assumption)
end
end
