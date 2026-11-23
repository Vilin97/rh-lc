module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host


theorem _root_.GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  first | exact @GlobalTheory.GLBallInt.integral_glBall_mem | exact GlobalTheory.GLBallInt.integral_glBall_mem | (intros; apply GlobalTheory.GLBallInt.integral_glBall_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host


theorem _root_.GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  first | exact @GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | exact GlobalTheory.CosetVanish.integral_coset_singular_eq_zero | (intros; apply GlobalTheory.CosetVanish.integral_coset_singular_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host


theorem _root_.GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  first | exact @GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic | exact GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic | (intros; apply GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfield

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.SmallFInF

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valLe (c : kˣ) : IsOpen {t : k | valuation k t ≤ valuation k (c : k)} := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have e : {t : k | valuation k t ≤ valuation k (c : k)} = (fun t => t / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ h0]
  rw [e]
  exact IsOpen.preimage (continuous_id.div_const _) Valuation.isOpen_integer

theorem isOpen_cosetM {n m : Type} [Fintype n] [Fintype m] (c : kˣ) (x : Matrix n m k) :
    IsOpen {y : Matrix n m k | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_valLe c).preimage (f := fun y : Matrix n m k => y i j - x i j) (by fun_prop)

theorem isCompact_ballM {n : Type} [Fintype n] (R : kˣ) :
    IsCompact {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} := by
  have h0 : 0 < valuation k (R : k) := zero_lt_iff.2 (by simp)
  have e : {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} =
      (fun z : Matrix n n k => (R : k) • z) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨(R : k)⁻¹ • y, fun i j => ?_, ?_⟩
      · rw [Valuation.mem_integer_iff]
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [inv_mul_le_iff₀ h0, mul_one]; exact hy i j
      · simp [smul_smul]
    · rintro ⟨z, hz, rfl⟩ i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hz i j))
  rw [e]
  exact isCompact_intMatrix.image (continuous_const_smul _)

end Helpers

theorem smallF_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ F J hJo hJK σ ν ϖ e hϖ he hcond hram hνF hapF c Ψ hΨ hΨF h
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨R, N, hbd, hper⟩ := GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock σ hϖ c hΨ h
  set Y := Y0 k σ * h.val with hY
  set cN : kˣ := ϖ ^ N with hcN
  set z : ℂ := (Fintype.card D : ℂ) / 2 with hz
  have hzF : ∀ u : kˣ, apow u z ∈ F := fun u => by
    have : apow u z = (apow u (1 / 2)) ^ (Fintype.card D) := by
      simp only [apow, hz]
      rw [← Complex.cpow_nat_mul]; congr 1; ring
    rw [this]; exact pow_mem (hapF u) _
  let Cs : Matrix A' A' k → Set (GL A' k) :=
    fun x => {g | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (cN : k)}
  have hCs_meas : ∀ x, MeasurableSet (Cs x) := fun x =>
    ((isOpen_cosetM cN x).preimage Units.continuous_val).measurableSet
  have hCs_eq : ∀ x y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) →
      Cs x = Cs y := by
    intro x y hxy
    ext g
    simp only [Cs, Set.mem_setOf_eq]
    constructor
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) ((Valuation.map_sub_swap _ _ _).le.trans (hxy i j))
      simpa using this
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) (hxy i j)
      simpa using this
  have hcoset : ∀ x, ∫ g in Cs x, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
    intro x
    by_cases hs : ∃ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) ∧ y.det = 0
    · obtain ⟨y, hy, hy0⟩ := hs
      rw [hCs_eq x y hy]
      rw [GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero (haarVol J) ν z hram cN y hy0]
      exact F.zero_mem
    · push_neg at hs
      exact GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield F hJo hJK ν z hϖ hcond hνF hzF cN x hs

  let L : AddSubgroup (Matrix A' A' k) :=
    { carrier := {Z | ∀ i j, valuation k (Z i j) ≤ valuation k (cN : k)}
      add_mem' := fun ha hb i j => Valuation.map_add_le _ (ha i j) (hb i j)
      zero_mem' := fun i j => by simp
      neg_mem' := fun ha i j => by simpa using ha i j }
  let q : Matrix A' A' k → Matrix A' A' k ⧸ L := QuotientAddGroup.mk
  have hq : ∀ x y : Matrix A' A' k, q x = q y ↔ ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k) := by
    intro x y
    rw [QuotientAddGroup.eq]
    refine forall₂_congr fun i j => ?_
    show valuation k ((-x + y) i j) ≤ _ ↔ _
    rw [show (-x + y) i j = -(x i j - y i j) by simp; ring, Valuation.map_neg]

  obtain ⟨T0, hT0⟩ := (isCompact_ballM (n := A') R).elim_finite_subcover
    (fun y : Matrix A' A' k => {x : Matrix A' A' k | ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k)})
    (fun y => isOpen_cosetM cN y)
    (fun x _ => Set.mem_iUnion.2 ⟨x, fun i j => by simp⟩)
  classical
  let T : Finset (Matrix A' A' k ⧸ L) := T0.image q
  set f : GL A' k → ℂ := fun g => Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z with hf
  have hdec : f = fun g => ∑ t ∈ T, ({g : GL A' k | q g.val = t}).indicator f g := by
    funext g
    by_cases h0 : f g = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Set.indicator_apply, h0]
    · have hΨ0 : Ψ (g.val * Y) ≠ 0 := fun h1 => h0 (by simp [hf, h1])
      have hB := hbd g.val hΨ0
      obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hT0 hB)
      have hqt : q g.val ∈ T := Finset.mem_image.2 ⟨y, hyT, ((hq _ _).2 hy).symm⟩
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite_eq]
      simp [hqt]
  show ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂(haarVol J) ∈ F
  change ∫ g, f g ∂(haarVol J) ∈ F
  by_cases hint : Integrable f (haarVol J)
  · have hmeas : ∀ t, MeasurableSet {g : GL A' k | q g.val = t} := by
      intro t
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
      have : {g : GL A' k | q g.val = q y} = Cs y := by
        ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
      rw [this]; exact hCs_meas y
    rw [hdec, integral_finsetSum _ (fun t _ => hint.indicator (hmeas t))]
    refine sum_mem fun t _ => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
    have hset : {g : GL A' k | q g.val = q y} = Cs y := by
      ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
    rw [integral_indicator (hmeas _), hset]
    have hc : ∫ g in Cs y, f g ∂(haarVol J) =
        ∫ g in Cs y, Ψ (y * Y) * ((ν (gdet g) : ℂ) * apow (gdet g) z) ∂(haarVol J) := by
      refine setIntegral_congr_fun (hCs_meas y) fun g hg => ?_
      have h1 : g.val = y + (g.val - y) := by abel
      have h2 : Ψ (g.val * Y) = Ψ (y * Y) := by
        rw [h1, hper y (g.val - y) (fun i j => hg i j)]
      simp only [hf, h2, mul_assoc]
    rw [hc, integral_const_mul]
    exact F.mul_mem (hΨF _) (hcoset y)
  · rw [integral_undef hint]; exact F.zero_mem

end GlobalTheory.SmallFInF
end
end
