module

public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.SingularCubic
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

-- Source module: GroundTheory.GlobalFields.ComplexMultiplication.ReductionNonsingularPoints

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

section E0

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

omit [DecidableEq (ResidueField 𝒪)] in
theorem add_notMem_of_notMem_range {X₁ Y₁ X₂ Y₂ : K} (h₁ : (curveK K W).Nonsingular X₁ Y₁)
    (hX₁ : X₁ ∉ Set.range ι) (h₂ : (curveK K W).Nonsingular X₂ Y₂) (hX₂ : X₂ ∉ Set.range ι)
    {x y : 𝒪} (h : (curveK K W).Nonsingular (ι x) (ι y)) :
    WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ ≠
      WeierstrassCurve.Affine.Point.some _ _ h := by
  intro hS
  have hn : (curveK K W).Nonsingular X₂ ((curveK K W).negY X₂ Y₂) :=
    (WeierstrassCurve.Affine.nonsingular_neg _ _).2 h₂
  obtain ⟨x₃, y₃, h₃, e, -, -⟩ := add_of_notMem_range' K W hn hX₂ h
  have hneg : -(WeierstrassCurve.Affine.Point.some _ _ h₂) =
      WeierstrassCurve.Affine.Point.some _ _ hn := WeierstrassCurve.Affine.Point.neg_some h₂
  have e' : WeierstrassCurve.Affine.Point.some _ _ h₁ =
      WeierstrassCurve.Affine.Point.some _ _ h₃ := by
    rw [← e, ← hS, ← hneg]; abel
  rw [WeierstrassCurve.Affine.Point.some.injEq] at e'
  exact hX₁ ⟨x₃, e'.1.symm⟩

theorem add_mem_E0Set_and_reducePoint_add {P Q : (curveK K W).Point} (hP : P ∈ E0Set K W)
    (hQ : Q ∈ E0Set K W) :
    P + Q ∈ E0Set K W ∧ reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  rcases point_cases K W P with rfl | ⟨X₁, Y₁, h₁, rfl, hX₁⟩ | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, reducePoint_zero, zero_add]; exact ⟨hQ, rfl⟩
  · rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · rw [reducePoint_some_notMem K W h₁ hX₁, reducePoint_some_notMem K W h₂ hX₂, add_zero]
      rcases point_cases K W (WeierstrassCurve.Affine.Point.some _ _ h₁ +
          WeierstrassCurve.Affine.Point.some _ _ h₂) with h0 | ⟨X, Y, h, hS, hX⟩ | ⟨x, y, h, hS⟩
      · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
      · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
      · exact absurd hS (add_notMem_of_notMem_range K W h₁ hX₁ h₂ hX₂ h)
    · have n₂ := hQ x₂ y₂ h₂ rfl
      obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₁ hX₁ h₂
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₂, e, ?_⟩
      rw [reducePoint_some_notMem K W h₁ hX₁, zero_add, reducePoint_some_integral K W h₂ n₂,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
  · have n₁ := hP x₁ y₁ h₁ rfl
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₂ hX₂ h₁
      rw [add_comm] at e
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₁, e, ?_⟩
      rw [reducePoint_some_notMem K W h₂ hX₂, add_zero, reducePoint_some_integral K W h₁ n₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
    · have n₂ := hQ x₂ y₂ h₂ rfl
      rw [reducePoint_some_integral K W h₁ n₁, reducePoint_some_integral K W h₂ n₂]
      by_cases hx : ρ x₁ = ρ x₂
      · by_cases hy : ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          rcases add_of_residue_neg K W h₁ h₂ n₁ n₂ hx hy with h0 | ⟨X, Y, h, hS, hX⟩
          · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
          · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
        · have hy' : ρ y₁ = ρ y₂ := by
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq n₁.1 n₂.1 hx with h | h
            · exact h
            · exact absurd h hy
          have hD : ρ (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0 := by
            intro h0; apply hy
            rw [map_add (f := _), map_add (f := _), map_add (f := _), map_mul] at h0
            simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₃, ← hx]
            linear_combination h0
          obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_eq K W h₁ h₂ n₁ n₂ hx hy' hD
          rw [e, e', reducePoint_some_integral K W h₃ n₃]
          exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩
      · obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_X_ne K W h₁ h₂ n₁ n₂ hx
        rw [e, e', reducePoint_some_integral K W h₃ n₃]
        exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩

def E0Subgroup : AddSubgroup (curveK K W).Point where
  carrier := E0Set K W
  zero_mem' := zero_mem_E0Set K W
  add_mem' hP hQ := (add_mem_E0Set_and_reducePoint_add K W hP hQ).1
  neg_mem' hP := (neg_mem_and_reduce K W hP).1

def reduceE0Hom : E0Subgroup K W →+ (curveRed W).Point where
  toFun P := reducePoint K W P
  map_zero' := reducePoint_zero K W
  map_add' P Q := (add_mem_E0Set_and_reducePoint_add K W P.2 Q.2).2

theorem reduceE0Hom_apply (P : E0Subgroup K W) : reduceE0Hom K W P = reducePoint K W P := rfl

end E0

end

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.ComplexMultiplication.TorsionReduction

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

section Scale

variable {R : Type*} [CommRing R]

def scaleCoeffs (W : WeierstrassCurve R) (a : R) : WeierstrassCurve R :=
  ⟨a * W.a₁, a ^ 2 * W.a₂, a ^ 3 * W.a₃, a ^ 4 * W.a₄, a ^ 6 * W.a₆⟩

theorem map_scaleCoeffs {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) (a : R) :
    (scaleCoeffs W a).map f = scaleCoeffs (W.map f) (f a) := by
  ext <;> simp [scaleCoeffs]

def scaleVariableChange {F : Type*} [Field F] {c : F} (hc : c ≠ 0) :
    WeierstrassCurve.VariableChange F :=
  ⟨(Units.mk0 c hc)⁻¹, 0, 0, 0⟩

theorem scaleVariableChange_smul {F : Type*} [Field F] (W : WeierstrassCurve F) {c : F}
    (hc : c ≠ 0) : scaleVariableChange hc • W = scaleCoeffs W c := by
  ext <;> simp [scaleVariableChange, scaleCoeffs, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆]

end Scale

section Torsion

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

theorem nsmul_ne_zero_of_notMem_range {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) {X Y : K}
    (h : (curveK K W).Nonsingular X Y) (hX : X ∉ Set.range ι) :
    n • WeierstrassCurve.Affine.Point.some _ _ h ≠ 0 := by
  intro hnP
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨z, w, v, hzm, hz0, -, -, hwv, hvu, hρv, hXz, hYw⟩ :=
    exists_zw_of_notMem_range K W h.1 hX
  have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
  set W' := scaleCoeffs W z with hW'
  have hC : scaleVariableChange hzK • W.map ι = W'.map ι := by
    rw [scaleVariableChange_smul, hW', map_scaleCoeffs]
  have : (W'.map ι).IsElliptic := hC ▸ inferInstance
  set v' : 𝒪 := ↑hvu.unit⁻¹ with hv'
  have hvv : v * v' = 1 := hvu.mul_val_inv
  have hvK : ι v * ι v' = 1 := by rw [← map_mul, hvv, map_one]
  have hwK : ι w = ι z ^ 3 * ι v := by rw [hwv, map_mul, map_pow]
  have hvK0 : ι v ≠ 0 := left_ne_zero_of_mul_eq_one hvK
  have hv'K : ι v' = (ι v)⁻¹ := eq_inv_of_mul_eq_one_right hvK
  have hx' : vcX (scaleVariableChange hzK) X = ι v' := by
    simp only [vcX, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero]
    rw [← hXz, hwK, hv'K]
    field_simp
  have hy' : vcY (scaleVariableChange hzK) X Y = ι (-v') := by
    simp only [vcY, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero, zero_mul]
    rw [← hYw, hwK, map_neg, hv'K]
    field_simp
  have h' : (curveK K W').Nonsingular (ι v') (ι (-v')) := by
    have := (nonsingular_vc (scaleVariableChange hzK) (W.map ι) X Y).2 h
    rw [hC, hx', hy'] at this
    exact this
  set φ := vcPointEquiv (scaleVariableChange hzK) hC
  have hφ : φ (.some _ _ h) = .some _ _ h' := by
    rw [vcPointEquiv_apply, vcPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx', hy'⟩

  have hρz : ρ z = 0 := residue_eq_zero_of_mem hzm
  have h1 : (W'.map ρ).a₁ = -2 * 0 := by simp [hW', scaleCoeffs, hρz]
  have h2 : (W'.map ρ).a₂ = -0 ^ 2 := by simp [hW', scaleCoeffs, hρz]
  have h3 : (W'.map ρ).a₃ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h4 : (W'.map ρ).a₄ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h6 : (W'.map ρ).a₆ = 0 := by simp [hW', scaleCoeffs, hρz]
  have hρv' : ρ v' = 1 := by
    have := congrArg ρ hvv
    rwa [map_mul, hρv, one_mul, map_one] at this
  have n' : (curveRed W').Nonsingular (ρ v') (ρ (-v')) :=
    origin_nonsingular (W'.map ρ) h3 h4 h6 (equation_residue W' (equation_of_map K W' h'.1))
      (by rw [hρv']; exact one_ne_zero)
  have hE0 : φ (.some _ _ h) ∈ E0Subgroup K W' := by
    rw [hφ]; exact mem_E0Set_some_integral K W' h' n'
  set Q : E0Subgroup K W' := ⟨_, hE0⟩
  have hnQ : n • Q = 0 := by
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    change n • φ _ = 0
    rw [← map_nsmul, hnP, map_zero]
  have hred : reduceE0Hom K W' Q = .some _ _ n' := by
    rw [reduceE0Hom_apply]
    change reducePoint K W' (φ _) = _
    rw [hφ, reducePoint_some_integral K W' h' n']
  have key : n • cuspHom (W'.map ρ) h3 h4 h6 0 h1 h2 (reduceE0Hom K W' Q) = 0 := by
    rw [← map_nsmul, ← map_nsmul, hnQ, map_zero, map_zero]
  rw [hred] at key
  change n • (ρ v' / (ρ (-v') - 0 * ρ v')) = 0 at key
  rw [map_neg, hρv'] at key
  apply hn
  simpa using key

end Torsion

section Good

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero {n : ℕ}
    (hn : (n : ResidueField 𝒪) ≠ 0) {P : (curveK K W).Point} (hnP : n • P = 0)
    (hP : reducePoint K W P = 0) : P = 0 := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rfl
  · exact absurd hnP (nsmul_ne_zero_of_notMem_range K W hn h hX)
  · rw [reducePoint_some_integral K W h (nonsingular_residue_of_isElliptic K W h.1)] at hP
    exact absurd hP (WeierstrassCurve.Affine.Point.some_ne_zero _)

theorem eq_of_reductionHom_eq_of_nsmul {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0)
    {P Q : (curveK K W).Point} (hP : n • P = 0) (hQ : n • Q = 0)
    (h : reductionHom K W P = reductionHom K W Q) : P = Q :=
  sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero K W hn
    (by rw [nsmul_sub, hP, hQ, sub_zero])
    (by rw [← reductionHom_apply, map_sub, h, sub_self]))

end Good

section Localization

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

end Localization

section NumberField

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (𝔮 : HeightOneSpectrum (𝓞 F))
  (W : WeierstrassCurve (𝔮.valuationSubringAtPrime F)) [W.IsElliptic] [DecidableEq F]
  [DecidableEq (ResidueField (𝔮.valuationSubringAtPrime F))]

end NumberField

end

end GroundTheory.Global
end
end
