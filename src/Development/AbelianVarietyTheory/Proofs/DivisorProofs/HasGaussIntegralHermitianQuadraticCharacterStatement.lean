module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNormStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralDiagonalHermitianFormMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingDiagonalNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMul

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem KSp.sgn_mul_of_isQuad : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s t
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold sgn
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE s t hs ht
    simp [hs, ht, this]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMulStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.localNormResidueSign_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  first | exact @GlobalTheory.KSp.sgn_mul_of_isQuad | exact GlobalTheory.KSp.sgn_mul_of_isQuad | (intros; apply GlobalTheory.KSp.sgn_mul_of_isQuad <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitian

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_gl_diagonal_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  intro F _ _ E _ _ c δ hE ν _ _ b hb hdet
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (c : E →+* E)) h2 (fun t => hE.invol t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => hE.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap F E ((Units.mk0 (f j) (hf0 j) : Fˣ) : F)) = diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]

end GlobalTheory.KSp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitianStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.exists_GL_diagonal_congruent_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  first | exact @GlobalTheory.KSp.exists_gl_diagonal_hermitian | exact GlobalTheory.KSp.exists_gl_diagonal_hermitian | (intros; apply GlobalTheory.KSp.exists_gl_diagonal_hermitian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacter

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

def sgnHom : Fˣ →* ℂ where
  toFun := sgn E
  map_one' := by simp only [sgn]; exact if_pos (one_mem _)
  map_mul' s t := GlobalTheory.T.localNormResidueSign_mul F E c δ hE s t

theorem sgn_inv (t : Fˣ) : sgn E t⁻¹ = sgn E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold sgn
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [if_pos ht, if_pos (h.mpr ht)]
  · rw [if_neg ht, if_neg (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring


include hE in
theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E) (D : ν → Fˣ) :
    sc F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (sgn E (D j) * ((nabs F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : nabs F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [nabs, map_inv]
  have e2 : sgn E (∏ j, D j)⁻¹ = ∏ j, sgn E (D j) := by
    rw [sgn_inv]; exact map_prod (sgnHom c hE) D Finset.univ
  have e3 : nabs F (∏ j, D j)⁻¹ = ∏ j, (nabs F (D j))⁻¹ := by
    simp [nabs, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  haveI : IsTopologicalRing E := (GlobalTheory.T.quadExt_topological_properties F E c δ hE).2.1
  obtain ⟨u, D', hQd⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE α Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i, (sgn E (s i) * ((nabs F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE ν b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale (Matrix α ν E) (Matrix α ν E) μ μ (sandwich U a) _ _ _
    (GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, sgn E (t i j) * (((nabs F (t i j))⁻¹ : ℝ) : ℂ) =
      (sgn E (s i) * (((nabs F (s i))⁻¹ : ℝ) : ℂ)) * (sgn E (D j) * (((nabs F (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [GlobalTheory.T.localNormResidueSign_mul F E c δ hE, GlobalTheory.SplitWeil.nabs_mul F, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GlobalTheory.KSp.GaussMain
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacterStatement

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  first | exact @GlobalTheory.KSp.GaussMain.hasGauss_herm | exact GlobalTheory.KSp.GaussMain.hasGauss_herm | (intros; apply GlobalTheory.KSp.GaussMain.hasGauss_herm <;> assumption)
end
end
