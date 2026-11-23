module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GamOneReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.IrreducibleOfMinimal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.JointEigenvectorExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.MatrixCoefficientEquation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.ProdFormula
import Mathlib.Analysis.Matrix.PosDef

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper

section

@[expose] public section

namespace PI.GGCardUniWork

open Finset Matrix Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

abbrev Pairs (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def uniMat (f : Pairs k → F) : Matrix (Fin k) (Fin k) F :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

theorem uniMat_upper (f : Pairs k → F) : (uniMat f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]

theorem uniMat_det (f : Pairs k → F) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]

noncomputable def uniGL (f : Pairs k → F) : GL (Fin k) F :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)

theorem uniGL_coe (f : Pairs k → F) : ((uniGL f : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = uniMat f := rfl

theorem isUni_uniGL (f : Pairs k → F) : IsUni k (uniGL f) := by
  unfold IsUni
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · simp [uniGL_coe, uniMat]
  · simp [uniGL_coe, uniMat, ne_of_gt h, not_lt.mpr h.le]

noncomputable def uniEquiv : {x : GL (Fin k) F // IsUni k x} ≃ (Pairs k → F) where
  toFun x p := (x.1 : Matrix (Fin k) (Fin k) F) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUni_uniGL f⟩
  left_inv x := by
    obtain ⟨x, hd, hl⟩ := x
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]

theorem card_pairs (k : ℕ) : Fintype.card (Pairs k) = k * (k - 1) / 2 := by
  have hI : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := fun j => by
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun i : Fin k => i < j) = Finset.Iio j by ext i; simp]
    exact Fin.card_Iio j
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [hI]
  have h3 : ∑ j : Fin k, (j : ℕ) = ∑ j ∈ Finset.range k, j := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h3, Finset.sum_range_id]

theorem cardUni : CardUni := by
  intro F _ _ k
  unfold cardU
  rw [Nat.card_congr (uniEquiv (F := F) (k := k)), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]

end PI.GGCardUniWork
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni

section

@[expose] public section

theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio

section

@[expose] public section

theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GgMatrixBoundOfLitOf

section

@[expose] public section

open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem ggMatrixBound_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hC : ConvScalar) (hR : GenericRatio) : GGMatrixBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef
  have hherm : A.IsHermitian := hH ι Fq k ψ X
  have hspec := hS X A _ hherm (fun w μ hw hAw =>
    hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw
      (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)

end PI.GGMatBoundW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.SpectrumPositiveSemidefinite

section

@[expose] public section

open Matrix

open scoped ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have gen : ∀ (A : Matrix X X ℂ) (hA : A.IsHermitian) (b : ℝ),
      (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ b ≤ r) →
      ∀ j, b ≤ hA.eigenvalues j := by
    intro A hA b h j
    have hv := hA.mulVec_eigenvectorBasis j
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    have key : ∀ v : X → ℂ, v ≠ 0 → A *ᵥ v = hA.eigenvalues j • v → b ≤ hA.eigenvalues j := by
      intro v hv0 hAv
      obtain ⟨r, hr, hbr⟩ := h v (hA.eigenvalues j : ℂ) hv0 (by rw [hAv]; ext i; simp)
      have hre : hA.eigenvalues j = r := by exact_mod_cast hr
      rw [hre]
      exact hbr
    exact key _ (fun h0 => hne (by ext i; simpa using congrFun h0 i)) hv
  have h1 : ((c : ℂ) • (1 : Matrix X X ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian := h1.sub hM
  have hNev : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → ((c : ℂ) • (1 : Matrix X X ℂ) - M) *ᵥ w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r := by
    intro w μ hw h
    have hMw : M *ᵥ w = ((c : ℂ) - μ) • w := by
      rw [Matrix.sub_mulVec] at h
      first
        | rw [Matrix.smul_mulVec] at h
        | rw [Matrix.smul_mulVec_assoc] at h
        | simp only [Matrix.smul_mulVec_assoc] at h
      rw [Matrix.one_mulVec] at h
      rw [sub_smul, ← h]
      abel
    obtain ⟨r, hr, _, hrc⟩ := hev w ((c : ℂ) - μ) hw hMw
    refine ⟨c - r, ?_, by linarith⟩
    push_cast
    linear_combination -hr
  constructor
  · refine hM.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen M hM 0 ?_ j
    intro w μ hw h
    obtain ⟨r, hr, h0, _⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · exact hN.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen _ hN 0 hNev j

end PI.GGMatBoundW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound

section

@[expose] public section

theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
end
end
