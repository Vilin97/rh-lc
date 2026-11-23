module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIntegralModelOfForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubringStatement
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfDuplicationEq

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_duplication_eq :
    ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W →
      W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V →
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) →
      x ∈ V ∧ y ∈ V := by
  intro V W x y δ hW hE hl hδ h
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hr : ∀ z : ℂ, z ∈ V → z ∈ (algebraMap V ℂ).range := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hr' : ∀ z : ℂ, z ∈ (algebraMap V ℂ).range → z ∈ V := by
    rintro z ⟨w, rfl⟩; exact w.2
  have hb₄ : W.b₄ ∈ V := by
    rw [WeierstrassCurve.b₄]
    exact add_mem (mul_mem (ofNat_mem V 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ V := by
    rw [WeierstrassCurve.b₆]
    exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem V 4) h₆)
  have hb₈ : W.b₈ ∈ V := by
    rw [WeierstrassCurve.b₈]
    refine sub_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact mul_mem (pow_mem h₁ 2) h₆
    · exact mul_mem (mul_mem (ofNat_mem V 4) h₂) h₆
    · exact mul_mem (mul_mem h₁ h₃) h₄
    · exact mul_mem h₂ (pow_mem h₃ 2)
    · exact pow_mem h₄ 2
  set l := 2 * y + W.a₁ * x + W.a₃ with hl_def
  have hx : x ∈ V := by
    refine hr' x (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := -(W.b₈ + l ^ 2 * δ))
      (c₁ := -(2 * W.b₆ + l ^ 2)) (c₂ := -W.b₄) (c₃ := 0) (hr _ ?_) (hr _ ?_) (hr _ ?_) (hr _ ?_) ?_)
    · exact neg_mem (add_mem hb₈ (mul_mem (pow_mem hl 2) hδ))
    · exact neg_mem (add_mem (mul_mem (ofNat_mem V 2) hb₆) (pow_mem hl 2))
    · exact neg_mem hb₄
    · exact zero_mem V
    · linear_combination h
  refine ⟨hx, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine hr' y (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := 0) (c₁ := 0)
    (c₂ := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (c₃ := W.a₁ * x + W.a₃)
    (hr _ (zero_mem V)) (hr _ (zero_mem V)) (hr _ ?_) (hr _ ?_) ?_)
  · exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆)
  · exact add_mem (mul_mem h₁ hx) h₃
  · linear_combination y ^ 2 * hE

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfDuplicationEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.mem_of_duplication_eq_weierstrass : ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W → W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V → x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) → x ∈ V ∧ y ∈ V := by
  first | exact @GlobalTheory.CMModel.mem_of_duplication_eq | exact GlobalTheory.CMModel.mem_of_duplication_eq | (intros; apply GlobalTheory.CMModel.mem_of_duplication_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSq

section

@[expose] public section

open PeriodPair WeierstrassCurve

namespace GlobalTheory

theorem weierstrassP_two_mul_mul_sq (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  rw [two_mul z] at h2 ⊢
  have hd : L.derivWeierstrassP z ≠ 0 := (derivWeierstrassP_eq_zero_iff L hz).not.mpr h2
  have hy : L.derivWeierstrassP z / 2 ≠
      (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
    intro h
    apply hd
    simp only [Affine.negY, latticeCurve] at h
    linear_combination h
  have h := latticePoint_add L z z
  rw [latticePoint_of_notMem L hz, latticePoint_of_notMem L h2,
    Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h
  have e := h.1
  rw [Affine.slope_of_Y_ne rfl hy] at e
  simp only [Affine.negY, Affine.addX, latticeCurve] at e
  have e2 : L.derivWeierstrassP z / 2 -
      (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z := by ring
  rw [e2] at e
  rw [e]
  field_simp
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSqStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq : ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice → L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 - 2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  first | exact @GlobalTheory.weierstrassP_two_mul_mul_sq | exact GlobalTheory.weierstrassP_two_mul_mul_sq | (intros; apply GlobalTheory.weierstrassP_two_mul_mul_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordsMemOfOdd

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem torsion_coords_mem_of_odd : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  intro L β u V N hmul hβ hΔ hN hodd hu r s t hint z hz hNz
  have h2z : 2 * z ∉ L.lattice := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    have e : z = (N : ℂ) * z - ((k : ℤ) • (2 * z)) := by
      rw [zsmul_eq_mul, hk]; push_cast; ring
    exact hz (e ▸ sub_mem hNz (L.lattice.smul_mem _ h))
  have hNz2 : (N : ℂ) * (2 * z) ∈ L.lattice := by
    have e : (N : ℂ) * (2 * z) = N * z + N * z := by ring
    rw [e]; exact add_mem hNz hNz
  obtain ⟨hP', -⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN z z hz hz hNz hNz
  obtain ⟨-, hδ⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN (2 * z) z h2z hz hNz2 hNz
  have dup := GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq L z hz h2z
  have sq := L.derivWeierstrassP_sq z hz
  set C : VariableChange ℂ := ⟨Units.mk0 u hu, r, s, t⟩ with hC
  have hCu : ((C.u⁻¹ : ℂˣ) : ℂ) = u⁻¹ := by simp [hC]
  have hCr : C.r = r := rfl
  have hCs : C.s = s := rfl
  have hCt : C.t = t := rfl
  set P := L.weierstrassP z with hPdef
  set P' := L.derivWeierstrassP z with hP'def
  set P2 := L.weierstrassP (2 * z) with hP2def
  have hD : 2 * ((P' / 2 - t - s * (P - r)) / u ^ 3) + (C • latticeCurve L).a₁ * ((P - r) / u ^ 2)
      + (C • latticeCurve L).a₃ = P' / u ^ 3 := by
    rw [variableChange_a₁, variableChange_a₃, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    field_simp
    ring
  apply GlobalTheory.T.mem_of_duplication_eq_weierstrass V (C • latticeCurve L) _ _ ((P2 - P) / u ^ 2) hint
  · rw [Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine]
    rw [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    linear_combination (norm := skip) (1 / 4 * u⁻¹ ^ 6) * sq
    field_simp
    ring
  · rw [hD]; exact hP'
  · exact hδ
  · rw [hD, variableChange_b₄, variableChange_b₆, variableChange_b₈, hCu, hCr]
    simp only [latticeCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (norm := skip) (u⁻¹ ^ 8) * (-dup + (2 * P + r) * sq)
    field_simp
    ring

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordsMemOfOddStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  first | exact @GlobalTheory.CMModel.torsion_coords_mem_of_odd | exact GlobalTheory.CMModel.torsion_coords_mem_of_odd | (intros; apply GlobalTheory.CMModel.torsion_coords_mem_of_odd <;> assumption)
end
end
