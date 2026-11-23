module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.InstCompactUG
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.KTypeExist
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.IsClosedDivisorComponent
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import GroundTheory.AutomorphicForms.RealGroupsKAK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.FiltrationCocycleLiftCriterion
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.MultOne
import GroundTheory.AutomorphicForms.RealIwasawaIntegration
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Pi

-- Source module: GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.MultOneC

section

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace KT

open Matrix MeasureTheory Complex Finset
open GroundTheory.Automorphic.ArchWhittaker (topologicalClosure_span_orbit eq_zero_of_forall_inner_map
  eq_smul_one_of_commute)
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

def transposeU (k : U2) : U2 :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℂ)ᵀ, Matrix.transpose_mem_unitaryGroup_iff.2 k.2⟩

@[simp] theorem coe_transposeU (k : U2) :
    ((transposeU k : U2) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := rfl

theorem transposeU_transposeU (k : U2) : transposeU (transposeU k) = k := Subtype.ext (by simp)

theorem transposeU_mul (k l : U2) : transposeU (k * l) = transposeU l * transposeU k :=
  Subtype.ext (by simp [Matrix.transpose_mul])

theorem continuous_transposeU : Continuous transposeU :=
  Continuous.subtype_mk (continuous_subtype_val.matrix_transpose) _

def transposeHomeo : U2 ≃ₜ U2 where
  toFun := transposeU
  invFun := transposeU
  left_inv := transposeU_transposeU
  right_inv := transposeU_transposeU
  continuous_toFun := continuous_transposeU
  continuous_invFun := continuous_transposeU

theorem map_transpose_μK : Measure.map transposeU μK = μK := by
  have hmeas : Measurable transposeU := continuous_transposeU.measurable
  haveI : μK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : (Measure.map (· * g) μK).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μK g
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  haveI : (Measure.map transposeU μK).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have e : (fun k => g * k) ∘ transposeU = transposeU ∘ (fun k => k * transposeU g) := by
      funext k; simp [transposeU_mul, transposeU_transposeU]
    rw [e, ← Measure.map_map hmeas (measurable_mul_const _), map_mul_right_eq_self]
  haveI : (Measure.map transposeU μK).IsHaarMeasure :=
    { lt_top_of_isCompact := fun K hK => measure_lt_top _ _
      toIsOpenPosMeasure := ⟨fun U hU hne => by
        rw [Measure.map_apply hmeas hU.measurableSet]
        exact (hU.preimage continuous_transposeU).measure_ne_zero μK
          (by obtain ⟨u, hu⟩ := hne; exact ⟨transposeU u, by simpa [transposeU_transposeU] using hu⟩)⟩ }
  haveI : IsProbabilityMeasure (Measure.map transposeU μK) :=
    by infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem integral_transpose_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E) :
    ∫ k, f (transposeU k) ∂μK = ∫ k, f k ∂μK := by
  have := integral_map_equiv (μ := μK) (transposeHomeo.toMeasurableEquiv) f
  have e : ((transposeHomeo.toMeasurableEquiv : U2 ≃ᵐ U2) : U2 → U2) = transposeU := rfl
  rw [e, map_transpose_μK] at this
  exact this.symm

theorem psi_transposeU_self (n : ℕ) (q : ℤ) (k : U2) : psi n q n (transposeU k) = psi n q n k := by
  simp [psi, Matrix.det_transpose]

theorem conj_psi_inv (n : ℕ) (q : ℤ) (i : ℕ) (k : U2) :
    conj (psi n q i k⁻¹) = psi n q i (transposeU k) := by
  simp only [psi, coe_inv_U2, det_star_U2, coe_transposeU, map_mul, map_pow, map_zpow₀,
    starRingEnd_self_apply, Matrix.transpose_apply, Matrix.det_transpose]
  simp [Matrix.star_apply]

theorem det_ne_zero_GL2C (g : GL2C) : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 (g : GL (Fin 2) ℂ).isUnit).ne_zero

noncomputable def iotaC (g : GL2C) : GL2C :=
  toGLC ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ (by rw [Matrix.det_transpose]; exact det_ne_zero_GL2C g)

theorem iotaC_mul (g h : GL2C) : iotaC (g * h) = iotaC h * iotaC g := by
  apply GL2C_ext; simp [iotaC, Matrix.transpose_mul]

theorem iotaC_kC (k : U2) : iotaC (kC k) = kC (transposeU k) := by
  apply GL2C_ext; simp [iotaC]

theorem iotaC_dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : iotaC (dC d₁ d₂ h₁ h₂) = dC d₁ d₂ h₁ h₂ := by
  apply GL2C_ext; simp only [iotaC, coe_toGLC, coe_dC]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_kakC (g : GL2C) : ∃ (k₁ k₂ : U2) (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂),
    g = kC k₁ * dC d₁ d₂ h₁ h₂ * kC k₂ := by
  obtain ⟨k₁, k₂, a, ha, hg⟩ := exists_KAK (g : GL (Fin 2) ℂ)
  refine ⟨k₁, k₂, a 0, a 1, ha 0, ha 1, GL2C_ext ?_⟩
  rw [hg]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_kC, coe_dC]
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem tC_dC_comm (a b d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    kC (tC a b) * dC d₁ d₂ h₁ h₂ = dC d₁ d₂ h₁ h₂ * kC (tC a b) := by
  apply GL2C_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_kC, coe_tC, coe_dC]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep GL2C H)

theorem inner_Q_map_dC_eq_zero (n : ℕ) (q : ℤ) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j)
    (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (x y : H) :
    ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ = 0 := by
  have hne : ((i : ℝ) - j) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
  set a : ℝ := Real.pi / ((i : ℝ) - j) with ha
  have h1 : ⟪σ (kC (tC a 0)) (Q σ n q j y), σ (kC (tC a 0)) (σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x))⟫_ℂ =
      ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ := by
    rw [UnitaryRep.inner_map_left, ← UnitaryRep.map_mul_apply, inv_mul_cancel, UnitaryRep.map_one,
      ContinuousLinearMap.one_apply]
  have h2 : ⟪σ (kC (tC a 0)) (Q σ n q j y), σ (kC (tC a 0)) (σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x))⟫_ℂ =
      -⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ := by
    rw [← UnitaryRep.map_mul_apply, tC_dC_comm, UnitaryRep.map_mul_apply, map_tC_Q σ n q hj,
      map_tC_Q σ n q hi, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      conj_exp_mul_exp]
    have : (((i : ℝ) + q) * a + ((n : ℝ) - i + q) * 0 - (((j : ℝ) + q) * a + ((n : ℝ) - j + q) * 0)) =
        Real.pi := by
      rw [ha]; field_simp; ring
    rw [this, show Complex.exp (I * (Real.pi : ℂ)) = -1 by rw [mul_comm, Complex.exp_pi_mul_I]]
    ring
  have : (2 : ℂ) * ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ = 0 := by
    linear_combination h1.symm.trans h2
  simpa using this

theorem inner_sum_smul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (u v : ι → H) (T : H →L[ℂ] H) :
    ⟪∑ j ∈ s, a j • u j, T (∑ i ∈ s, b i • v i)⟫_ℂ =
      ∑ j ∈ s, ∑ i ∈ s, conj (a j) * b i * ⟪u j, T (v i)⟫_ℂ := by

  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, mul_assoc]

theorem map_kC_of_mem {n : ℕ} {q : ℤ} {x : H} (hx : x ∈ W σ n q) (l : U2) :
    σ (kC l) x = ∑ i ∈ range (n + 1),
      ((n.choose i : ℂ) * psi n q i l) • (((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x) := by
  conv_lhs => rw [← (mem_W σ).1 hx]
  rw [map_P]

theorem inner_map_kak {n : ℕ} {q : ℤ} {x y : H} (hx : x ∈ W σ n q) (hy : y ∈ W σ n q)
    (k₁ k₂ : U2) (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    ⟪y, σ (kC k₁ * dC d₁ d₂ h₁ h₂ * kC k₂) x⟫_ℂ =
      ∑ i ∈ range (n + 1), ((n.choose i : ℂ) ^ 2 * psi n q i (transposeU k₁) * psi n q i k₂) *
        ⟪((normSqInt n q)⁻¹ : ℂ) • Q σ n q i y,
          σ (dC d₁ d₂ h₁ h₂) (((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x)⟫_ℂ := by
  rw [UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right,
    ← map_inv, map_kC_of_mem σ hx, map_kC_of_mem σ hy]
  rw [show (σ (dC d₁ d₂ h₁ h₂)) = (σ (dC d₁ d₂ h₁ h₂) : H →L[ℂ] H) from rfl, inner_sum_smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single j]
  · rw [map_mul, conj_psi_inv, map_natCast]; ring
  · intro i hi hij
    rw [map_smul, inner_smul_left, inner_smul_right,
      inner_Q_map_dC_eq_zero σ n q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hij]
    ring
  · intro h; exact absurd hj h

theorem inner_map_iotaC {n : ℕ} {q : ℤ} {x y : H} (hx : x ∈ W σ n q) (hy : y ∈ W σ n q) (g : GL2C) :
    ⟪y, σ (iotaC g) x⟫_ℂ = ⟪y, σ g x⟫_ℂ := by
  obtain ⟨k₁, k₂, d₁, d₂, h₁, h₂, rfl⟩ := exists_kakC g
  rw [iotaC_mul, iotaC_mul, iotaC_kC, iotaC_kC, iotaC_dC, ← mul_assoc, inner_map_kak σ hx hy,
    inner_map_kak σ hx hy, transposeU_transposeU]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

noncomputable def compr (n : ℕ) (q : ℤ) (g : GL2C) : W σ n q →L[ℂ] W σ n q :=
  ((PL σ n q).comp ((σ g).comp (W σ n q).subtypeL)).codRestrict (W σ n q)
    (fun _ => P_mem_alt σ n q _)

@[simp] theorem coe_compr_apply (n : ℕ) (q : ℤ) (g : GL2C) (v : W σ n q) :
    ((compr σ n q g v : W σ n q) : H) = P σ n q (σ g v) := rfl

theorem inner_compr (n : ℕ) (q : ℤ) (g : GL2C) (v w : W σ n q) :
    ⟪(w : H), (compr σ n q g v : H)⟫_ℂ = ⟪(w : H), σ g v⟫_ℂ := by
  rw [coe_compr_apply, inner_P_of_mem σ w.2]

theorem inner_compr_compr (n : ℕ) (q : ℤ) (g h : GL2C) (v w : W σ n q) :
    ⟪(w : H), (compr σ n q g (compr σ n q h v) : H)⟫_ℂ = ((normSqInt n q)⁻¹ : ℂ) *
      ∫ k, conj (psi n q n k) * ⟪(w : H), σ (g * kC k * h) v⟫_ℂ ∂μK := by
  rw [inner_compr, coe_compr_apply, UnitaryRep.inner_map_right, P, inner_smul_right, Q,
    inner_Kint_right σ (continuous_conj_psi n q n)]
  congr 1
  congr 1; funext k
  rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply,
    mul_assoc]

theorem compr_iotaC (n : ℕ) (q : ℤ) (g : GL2C) : compr σ n q (iotaC g) = compr σ n q g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, inner_compr, inner_compr,
    inner_map_iotaC σ v.2 w.2]

theorem compr_comm (n : ℕ) (q : ℤ) (g h : GL2C) :
    compr σ n q g * compr σ n q h = compr σ n q h * compr σ n q g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, inner_compr_compr, ← compr_iotaC σ n q h, ← compr_iotaC σ n q g,
    inner_compr_compr]
  congr 1
  set F : U2 → ℂ := fun k => conj (psi n q n k) * ⟪(w : H), σ (iotaC h * kC k * iotaC g) v⟫_ℂ with hF
  rw [← integral_transpose_K F]
  congr 1; funext k
  simp only [hF]
  rw [psi_transposeU_self, ← iotaC_kC, ← inner_map_iotaC σ v.2 w.2 (g * kC k * h), iotaC_mul,
    iotaC_mul]
  simp only [mul_assoc]

end KT

end GroundTheory.Automorphic.ArchWhittakerC
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws

section

@[expose] public section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem T_cont (n : ℕ) (q : ℤ) : Continuous (T n q) :=
  continuous_const.mul (KT.continuous_conj_psi n q n)

private theorem T_inv (n : ℕ) (q : ℤ) (k : U2) : T n q k⁻¹ = conj (T n q k) := by
  simp only [T, KT.psi_self_inv, map_mul, map_inv₀, Complex.conj_ofReal, starRingEnd_self_apply]

private theorem T_idem (n : ℕ) (q : ℤ) (k : U2) : ∫ h, T n q h * T n q (h⁻¹ * k) ∂μK = T n q k := by
  have hc := KT.collapse (H := ℂ) n q (fun i => conj (KT.psi n q i k))
  have e : ∀ h, T n q h * T n q (h⁻¹ * k) = ((KT.normSqInt n q : ℂ))⁻¹ * (((KT.normSqInt n q : ℂ))⁻¹ *
      (conj (KT.psi n q n h) • ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℂ) * KT.psi n q i h) • conj (KT.psi n q i k))) := by
    intro h

    simp only [T, KT.psi_inv_mul, map_sum, map_mul, map_natCast, starRingEnd_self_apply, smul_eq_mul]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul]
  simp only [smul_eq_mul] at hc ⊢
  rw [hc]
  rfl

private theorem int_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type} [Fintype ι]
    (j : ι) {G : (ι → U2) → E} (hG : Continuous G) :
    ∫ m, G m ∂(Measure.pi fun _ : ι => μK) =
      ∫ m, ∫ u, G (Function.update m j u) ∂μK ∂(Measure.pi fun _ : ι => μK) := by
  have h1 : ∀ u : U2, ∫ m, G (m * Pi.mulSingle j u) ∂(Measure.pi fun _ : ι => μK) = ∫ m, G m ∂(Measure.pi fun _ : ι => μK) :=
    fun u => integral_mul_right_eq_self G _
  have h2 : ∫ m, G m ∂(Measure.pi fun _ : ι => μK) =
      ∫ u, ∫ m, G (m * Pi.mulSingle j u) ∂(Measure.pi fun _ : ι => μK) ∂μK := by
    simp only [h1, integral_const, probReal_univ, one_smul]
  rw [h2, integral_integral_swap]
  · congr 1; funext m
    rw [← integral_mul_left_K (fun u => G (Function.update m j u)) (m j)]
    congr 1; funext u; congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  · refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact hG.comp (continuous_snd.mul ((continuous_mulSingle j).comp continuous_fst))

section

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] (C : Co K ι)

private noncomputable def glH (i : ι) : GL2C →* G1 K 2 :=
  MonoidHom.mk' (fun g => C.gl i g.1) fun a b => (coLaws K ι C).2.2.2.2.1 i a.1 b.1

private theorem glH_cont (i : ι) : Continuous (glH C i) :=
  ((coLaws K ι C).2.2.2.1 i).comp continuous_subtype_val

private theorem continuous_arch_compact_inclusion : Continuous (arc1 : archCompact K 2 → G1 K 2) :=
  continuous_archP.comp continuous_subtype_val

private theorem int_κ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : archCompact K 2 → E) :
    ∫ k, f k ∂C.κ₂ = ∫ m, f ((C.Φ 2).symm m) ∂(Measure.pi fun _ : ι => μK) :=
  (C.Φ 2).symm.toHomeomorph.measurableEmbedding.integral_map f

private theorem idemA (n : ι → ℕ) (q : ι → ℤ) : IdemA C.κ₂ (C.p n q) := by
  refine { haar := (coLaws K ι C).1, cont := ?_, star := ?_, idem := ?_ }
  · exact continuous_finsetProd _ fun i _ => (T_cont _ _).comp ((continuous_apply i).comp (C.Φ 2).continuous)
  · intro k
    simp only [Co.p, map_inv, Pi.inv_apply, T_inv, map_prod]
  · intro k
    rw [int_κ]
    have e : ∀ m : ι → U2, C.p n q ((C.Φ 2).symm m) * C.p n q (((C.Φ 2).symm m)⁻¹ * k) =
        ∏ i, (T (n i) (q i) (m i) * T (n i) (q i) ((m i)⁻¹ * C.Φ 2 k i)) := by
      intro m
      simp only [Co.p, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply, Pi.inv_apply, Finset.prod_mul_distrib]
    simp_rw [e]
    rw [integral_fintype_prod_eq_prod (fun i x => T (n i) (q i) x * T (n i) (q i) (x⁻¹ * C.Φ 2 k i))]
    simp only [T_idem]
    rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : UnitaryRep (G1 K 2) H)

private noncomputable def PiH (i : ι) (n : ℕ) (q : ℤ) (v : H) : H := ∫ m, T n q m • ρ (C.un i m) v ∂μK

private noncomputable def sg (i : ι) : UnitaryRep GL2C H := ρ.compHom (glH C i) (glH_cont C i)

private theorem sg_apply (i : ι) (g : GL2C) (v : H) : sg C ρ i g v = ρ (C.gl i g.1) v := rfl

private theorem sg_kC (i : ι) (m : U2) (v : H) : sg C ρ i (kC m) v = ρ (C.un i m) v := by
  rw [sg_apply, (coLaws K ι C).2.2.1 i m]

private theorem PiH_eq (i : ι) (n : ℕ) (q : ℤ) (v : H) : PiH C ρ i n q v = KT.P (sg C ρ i) n q v := by
  simp only [PiH, KT.P, KT.Q, KT.Kint, T, mul_smul, sg_kC]
  rw [integral_smul]

private theorem PiH_int (i : ι) (n : ℕ) (q : ℤ) (v : H) :
    Integrable (fun m => T n q m • ρ (C.un i m) v) μK := by
  refine KT.integrable_of_continuous ((T_cont n q).smul ?_)
  simp only [← sg_kC]
  exact KT.continuous_orbit_K (sg C ρ i) v

private theorem PiH_mem (i : ι) (n : ℕ) (q : ℤ) (τ : Submodule ℂ H) (hc : IsClosed (τ : Set H))
    (hi : ∀ g, ∀ v ∈ τ, ρ g v ∈ τ) (v : H) (hv : v ∈ τ) : PiH C ρ i n q v ∈ τ :=
  Convex.integral_mem (τ.restrictScalars ℝ).convex hc
    (Eventually.of_forall fun m => τ.smul_mem _ (hi _ _ hv)) (PiH_int C ρ i n q v)

private theorem PiH_comm (i : ι) (n : ℕ) (q : ℤ) (h : G1 K 2) (hh : ∀ b, Commute h (C.gl i b)) (v : H) :
    PiH C ρ i n q (ρ h v) = ρ h (PiH C ρ i n q v) := by
  simp only [PiH]
  rw [← ContinuousLinearMap.integral_comp_comm _ (PiH_int C ρ i n q v)]
  congr 1; funext m
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, (coLaws K ι C).2.2.1 i m, (hh _).eq]

private theorem part1 (i : ι) (n : ℕ) (q : ℤ) : ∃ P : H →L[ℂ] H, (∀ v, P v = PiH C ρ i n q v) ∧ IsSelfAdjoint P ∧ P ∘L P = P ∧
        (∀ a b, Commute (P ∘L ρ (C.gl i a) ∘L P) (P ∘L ρ (C.gl i b) ∘L P)) ∧
        (∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (ρ h)) ∧
        ∀ τ : Submodule ℂ H, IsClosed (τ : Set H) → (∀ g, ∀ v ∈ τ, ρ g v ∈ τ) → ∀ v ∈ τ, P v ∈ τ := by
  have hP : ∀ v, KT.PL (sg C ρ i) n q v = PiH C ρ i n q v := fun v => (PiH_eq C ρ i n q v).symm
  refine ⟨KT.PL (sg C ρ i) n q, hP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    exact KT.inner_P_left (sg C ρ i) n q x y
  · ext1 v
    exact KT.P_P (sg C ρ i) n q v
  · intro a b
    ext1 v
    have key := congrArg (fun T => ((T ⟨KT.P (sg C ρ i) n q v, KT.P_mem_alt _ n q v⟩ : KT.W (sg C ρ i) n q) : H))
      (KT.compr_comm (sg C ρ i) n q ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
    simp only [ContinuousLinearMap.mul_apply, KT.coe_compr_apply, sg_apply] at key
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, KT.PL_apply, KT.P_P]
    simpa only [KT.P_P, sg_apply] using key
  · intro h hh
    ext1 v
    simp only [ContinuousLinearMap.mul_apply, hP]
    exact PiH_comm C ρ i n q h hh v
  · intro τ hc hi v hv
    rw [hP]
    exact PiH_mem C ρ i n q τ hc hi v hv

private theorem part4 (i : ι) (v : H) (hv : ∀ n q g, PiH C ρ i n q (ρ g v) = 0) : v = 0 := by
  let Wd : Submodule ℂ H :=
    { carrier := {y | ∀ (n : ℕ) (q : ℤ) (g : G1 K 2), KT.P (sg C ρ i) n q (ρ g y) = 0}
      add_mem' := fun {x y} hx hy n q g => by rw [map_add (f := _), KT.P_add, hx, hy, add_zero]
      zero_mem' := fun n q g => by rw [map_zero]; simpa using KT.P_smul (sg C ρ i) n q 0 0
      smul_mem' := fun c x hx n q g => by rw [map_smul, KT.P_smul, hx, smul_zero] }
  have hcl : IsClosed (Wd : Set H) := by
    have : (Wd : Set H) = ⋂ (n : ℕ) (q : ℤ) (g : G1 K 2), {y | KT.PL (sg C ρ i) n q (ρ g y) = 0} := by
      ext y; simp [Wd]
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun q => isClosed_iInter fun g =>
      isClosed_eq ((KT.PL (sg C ρ i) n q).continuous.comp (ρ g).continuous) continuous_const
  haveI : CompleteSpace Wd := hcl.completeSpace_coe
  have hinv : ρ.IsInvariant Wd := fun g y hy n q g' => by
    rw [← UnitaryRep.map_mul_apply]; exact hy n q (g' * g)
  let σ' : UnitaryRep GL2C Wd := (ρ.restrict Wd hinv).compHom (glH C i) (glH_cont C i)
  have hQ : ∀ (n : ℕ) (q : ℤ) (y : Wd), KT.Q σ' n q n y = 0 := by
    intro n q y
    apply Subtype.ext
    have h1 : ((KT.Q σ' n q n y : Wd) : H) = KT.Q (sg C ρ i) n q n (y : H) := by
      simp only [KT.Q, KT.Kint]
      exact (ContinuousLinearMap.integral_comp_comm Wd.subtypeL (KT.integrable_Kint σ' (KT.continuous_conj_psi n q n) y)).symm
    have h2 := y.2 n q 1
    rw [UnitaryRep.map_one_apply, KT.P] at h2
    have hne : ((KT.normSqInt n q : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (KT.normSqInt_pos n q).ne')
    rw [h1, (smul_eq_zero.1 h2).resolve_left hne]
    rfl
  have hvW : v ∈ Wd := fun n q g => by rw [← PiH_eq]; exact hv n q g
  exact congrArg Subtype.val (KT.eq_zero_of_forall_Q_eq_zero σ' hQ ⟨v, hvW⟩)

variable (n : ι → ℕ) (q : ι → ℤ)

private theorem arch_compact_inclusion_mul (a b : archCompact K 2) : (arc1 (a * b) : G1 K 2) = arc1 a * arc1 b :=
  map_mul (archP K 2) _ _

private noncomputable def pH (e : archCompact K 2 → ℂ) (v : H) : H := ∫ k, e k • ρ (arc1 k) v ∂C.κ₂

private noncomputable def cS (S : Finset ι) (m : ι → U2) : archCompact K 2 := (C.Φ 2).symm (S.piecewise m 1)

private noncomputable def wS (S : Finset ι) (v : H) (m : ι → U2) : H :=
  (∏ i ∈ S, T (n i) (q i) (m i)) • ρ (arc1 (cS C S m)) v

private theorem cS_cont (S : Finset ι) : Continuous (cS C S) :=
  (C.Φ 2).symm.continuous.comp (continuous_pi fun i => by
    by_cases hi : i ∈ S
    · simpa [Finset.piecewise, hi] using continuous_apply i
    · simpa [Finset.piecewise, hi] using continuous_const)

private theorem wS_cont (S : Finset ι) (v : H) : Continuous (wS C ρ n q S v) :=
  (continuous_finsetProd _ fun i _ => (T_cont _ _).comp (continuous_apply i)).smul
    ((ρ.continuous_orbit v).comp (continuous_arch_compact_inclusion.comp (cS_cont C S)))

private noncomputable def AS (S : Finset ι) (v : H) : H := ∫ m, wS C ρ n q S v m ∂(Measure.pi fun _ : ι => μK)

private theorem AS_empty (v : H) : AS C ρ n q ∅ v = v := by
  have : ∀ m, wS C ρ n q ∅ v m = v := by
    intro m
    have h1 : cS C ∅ m = 1 := by
      rw [cS, Finset.piecewise_empty]; exact map_one (C.Φ 2).symm
    have h2 : (arc1 (1 : archCompact K 2) : G1 K 2) = 1 := map_one (archP K 2)
    rw [wS, h1, h2, Finset.prod_empty, one_smul, UnitaryRep.map_one_apply]
  simp only [AS, this, integral_const, probReal_univ, one_smul]

private theorem cS_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (u : U2) (m : ι → U2) :
    cS C (insert j S) (Function.update m j u) = (C.Φ 2).symm (Pi.mulSingle j u) * cS C S m := by
  rw [cS, cS, ← map_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp [Finset.piecewise, hj]
  · by_cases hs : i ∈ S <;> simp [Finset.piecewise, hi, hs]

private theorem AS_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (v : H) :
    AS C ρ n q (insert j S) v = PiH C ρ j (n j) (q j) (AS C ρ n q S v) := by
  have e : ∀ m, ∫ u, wS C ρ n q (insert j S) v (Function.update m j u) ∂μK =
      KT.PL (sg C ρ j) (n j) (q j) (wS C ρ n q S v m) := by
    intro m
    rw [KT.PL_apply, ← PiH_eq, PiH]
    congr 1; funext u
    have hp : ∏ i ∈ S, T (n i) (q i) (Function.update m j u i) = ∏ i ∈ S, T (n i) (q i) (m i) :=
      Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
    rw [wS, wS, Finset.prod_insert hj, Function.update_self, cS_insert C hj, hp, arch_compact_inclusion_mul, UnitaryRep.map_mul_apply,
      mul_smul, map_smul]
    rfl
  simp only [AS]
  rw [int_update j (wS_cont C ρ n q _ v)]
  simp_rw [e]
  rw [ContinuousLinearMap.integral_comp_comm _
    ((wS_cont C ρ n q S v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), KT.PL_apply, ← PiH_eq]

private theorem AS_univ (v : H) : AS C ρ n q Finset.univ v = pH C ρ (C.p n q) v := by
  rw [pH, int_κ, AS]
  congr 1; funext m
  simp only [wS, cS, Co.p, Finset.piecewise_univ, ContinuousMulEquiv.apply_symm_apply]

private theorem part2 (v : H) : pH C ρ (C.p n q) v = v ↔ ∀ i, PiH C ρ i (n i) (q i) v = v := by
  constructor
  · intro h j
    have h1 : AS C ρ n q Finset.univ v = PiH C ρ j (n j) (q j) (AS C ρ n q (Finset.univ.erase j) v) := by
      rw [← AS_insert C ρ n q (Finset.notMem_erase j _), Finset.insert_erase (Finset.mem_univ j)]
    rw [AS_univ, h] at h1
    have h2 : ∀ x, PiH C ρ j (n j) (q j) (PiH C ρ j (n j) (q j) x) = PiH C ρ j (n j) (q j) x := fun x => by
      simp only [PiH_eq]; exact KT.P_P _ _ _ x
    exact (congrArg _ h1).trans ((h2 _).trans h1.symm)
  · intro h
    have : ∀ S : Finset ι, AS C ρ n q S v = v := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact AS_empty C ρ n q v
      | insert j S hj ih => rw [AS_insert C ρ n q hj, ih, h]
    rw [← AS_univ, this]

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.piLaws :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure], (∀ i n q, ∃ P : LL μ →L[ℂ] LL μ, (∀ v, P v = C.Pi μ i n q v) ∧ IsSelfAdjoint P ∧ P ∘L P = P ∧
        (∀ a b, Commute (P ∘L rightRegularRep (Gam K 2) μ (C.gl i a) ∘L P) (P ∘L rightRegularRep (Gam K 2) μ (C.gl i b) ∘L P)) ∧
        (∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (rightRegularRep (Gam K 2) μ h)) ∧
        ∀ τ : Submodule ℂ (LL μ), CuspIrr μ τ → ∀ v ∈ τ, P v ∈ τ) ∧
      (∀ n q v, pOp μ C.κ₂ (C.p n q) v = v ↔ ∀ i, C.Pi μ i (n i) (q i) v = v) ∧ (∀ n q, IdemA C.κ₂ (C.p n q)) ∧
      ∀ i (v : LL μ), (∀ n q (g : G1 K 2), C.Pi μ i n q (rightRegularRep (Gam K 2) μ g v) = 0) → v = 0 := by
  intro K _ _ _ ι _ C μ _
  refine ⟨fun i n q => ?_, fun n q v => part2 C (rightRegularRep (Gam K 2) μ) n q v, fun n q => idemA C n q,
    fun i v hv => part4 C (rightRegularRep (Gam K 2) μ) i v hv⟩
  obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := part1 C (rightRegularRep (Gam K 2) μ) i n q
  exact ⟨P, h1, h2, h3, h4, h5, fun τ hτ v hv => h6 τ hτ.closed hτ.inv v hv⟩
end
end
