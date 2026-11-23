module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitaryStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesWeylHeisenbergSchrodinger

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_fou : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ μ _ w φ
  obtain ⟨β, hβ, hsym, -, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI : IsTopologicalAddGroup (Matrix α ν E) := (hM α ν).2.grp
  have hh : ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) (x : Matrix α ν E),
      heisFun c ψ Q w φ x = ψ (β x w.toCols₂ + 2⁻¹ * β w.toCols₁ w.toCols₂) * φ (x + w.toCols₁) := by
    intro w φ x
    show ψ (pr c Q _ _ + 2⁻¹ * pr c Q _ _) * _ = _
    rw [← hβ, ← hβ]
  have hJ : w * stdJ ν E = fromCols (-w.toCols₂) w.toCols₁ := by
    ext i (j | j) <;> simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, fromBlocks, toCols₁, toCols₂]
  funext x
  simp only [fou]
  rw [hh, hJ]
  simp only [four, hh, toCols₁_fromCols, toCols₂_fromCols, ← hβ]
  set x₁ := w.toCols₁
  set y₁ := w.toCols₂
  rw [← integral_add_right_eq_self (μ := μ) (fun y => ψ (β x y) * (ψ (β y x₁ + 2⁻¹ * β (-y₁) x₁) * φ (y + -y₁))) y₁,
    ← integral_const_mul]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add (f := _), map_neg, LinearMap.add_apply, LinearMap.neg_apply, hsym y x₁, hsym y₁ x₁]
  ring

end GlobalTheory.KSp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesWeylHeisenbergSchrodingerStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_fou | exact GlobalTheory.KSp.heisFun_fou | (intros; apply GlobalTheory.KSp.heisFun_fou <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompat

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_parFun : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ _ χ _ _ p hp w φ
  have hc : ∀ z, c (c z) = z := hE.invol
  have hp0 : (mat c p).toBlocks₂₁ = 0 := hp
  set A := (mat c p).toBlocks₁₁ with hA
  set B := (mat c p).toBlocks₁₂ with hB
  set D := (mat c p).toBlocks₂₂ with hD
  have key : ∀ x y : Matrix α ν E, fromCols x y * mat c p = fromCols (x * A) (x * B + y * D) := by
    intro x y
    conv_lhs => rw [← fromBlocks_toBlocks (mat c p)]
    rw [fromCols_mul_fromBlocks, hp0]
    simp [hA, hB, hD]
  have spl : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp

  have h1 : ∀ x y : Matrix α ν E, form c Q (fromCols (x * A) 0) (fromCols 0 (y * D)) = form c Q (fromCols x 0) (fromCols 0 y) := by
    intro x y
    have h := form_mul c Q p (fromCols x 0) (fromCols 0 y)
    change form c Q (fromCols x 0 * mat c p) (fromCols 0 y * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x * A) (x * B), form_add_left, form_right_right, add_zero] at h
    exact h

  have h2 : ∀ x x' : Matrix α ν E, form c Q (fromCols (x' * A) 0) (fromCols 0 (x * B)) = form c Q (fromCols (x * A) 0) (fromCols 0 (x' * B)) := by
    intro x x'
    have h := form_mul c Q p (fromCols x' 0) (fromCols x 0)
    change form c Q (fromCols x' 0 * mat c p) (fromCols x 0 * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x' * A) (x' * B), spl (x * A) (x * B), form_add_left, form_add_right, form_add_right,
      form_left_left, form_left_left, form_right_right, form_swap c hc hQ (fromCols (x * A) 0) (fromCols 0 (x' * B))] at h
    linear_combination h
  have hw : w * mat c p = fromCols (w.toCols₁ * A) (w.toCols₁ * B + w.toCols₂ * D) := by
    conv_lhs => rw [← fromCols_toCols w]
    exact key _ _
  funext x
  simp only [heisFun, parFun, pr, hw, toCols₁_fromCols, toCols₂_fromCols]
  rw [← hA, ← hB]
  have key2 : ∀ (a b c d : F) (s t : ℂ), a + b = c + d → ψ a * (s * (ψ b * t)) = s * (ψ c * (ψ d * t)) := by
    intro a b c d s t h
    rw [show ψ a * (s * (ψ b * t)) = s * (ψ (a + b) * t) by rw [AddChar.map_add_eq_mul]; ring, h,
      AddChar.map_add_eq_mul]
    ring
  rw [Matrix.add_mul x w.toCols₁ A, Matrix.add_mul x w.toCols₁ B]
  simp only [e1, e2, form_add_left, form_add_right, h1]
  rw [h2 x w.toCols₁]
  apply key2
  ring

end GlobalTheory.KSp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompatStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.siegelParabolic_operators_heisenberg_compat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_parFun | exact GlobalTheory.KSp.heisFun_parFun | (intros; apply GlobalTheory.KSp.heisFun_parFun <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenberg

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem weil_heis_intertwine : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hK
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ w : Matrix α (ν ⊕ ν) E, Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * mat c g)}
      one_mem' := by
        intro w
        have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
        rw [map_one, h1, Matrix.mul_one, mul_one, one_mul]
      mul_mem' := by
        intro g h hg hh w
        have hm : mat c (g * h) = mat c g * mat c h := rfl
        rw [map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc, hm, Matrix.mul_assoc]
      inv_mem' := by
        intro g hg w
        have h1 : mat c g⁻¹ * mat c g = 1 := by
          change (((g⁻¹ * g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
          rw [inv_mul_cancel]; rfl
        have h2 := hg (w * mat c g⁻¹)
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] at h2
        have h3 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h4 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        show Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹)
        calc Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * (ω g * Heisenberg₂ c hψ Q w) * ω g⁻¹ := by
              simp only [← mul_assoc, h3, one_mul]
          _ = ω g⁻¹ * (Heisenberg₂ c hψ Q (w * mat c g⁻¹) * ω g) * ω g⁻¹ := by rw [h2]
          _ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹) := by simp only [mul_assoc, h4, mul_one] }
  have hsieg : sieg c ν ≤ U := by
    intro p hp w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.par p hp]
    exact GlobalTheory.T.siegelParabolic_operators_heisenberg_compat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη p hp w φ
  have hweyl : weyl c ν ∈ U := by
    intro w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.wey]
    have hs : ∀ f : Matrix α ν E → ℂ, heisFun c ψ Q w (κ • f) = κ • heisFun c ψ Q w f := by
      intro f; funext x; simp only [heisFun, Pi.smul_apply, smul_eq_mul]; ring
    rw [hs, GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger F E c δ hE α ν Q hQ ψ μ w φ]
    rfl
  have hU := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hweyl
  intro g w
  have hg : g ∈ U := hU ▸ Subgroup.mem_top g
  exact hg w

end GlobalTheory.KSp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenbergStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.weilRepresentation_intertwines_heisenberg : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  first | exact @GlobalTheory.KSp.weil_heis_intertwine | exact GlobalTheory.KSp.weil_heis_intertwine | (intros; apply GlobalTheory.KSp.weil_heis_intertwine <;> assumption)
end
end
