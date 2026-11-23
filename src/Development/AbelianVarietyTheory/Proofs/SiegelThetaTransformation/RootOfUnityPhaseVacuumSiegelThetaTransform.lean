module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualVacuumGaussianShapeRootOfUnityPhases
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMul
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMul
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticEqParabolicJParabolicJParabolic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSIntertwines
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitarySiegelThetaTransformationLawStandar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhase

section

@[expose] public section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ParabValues

open GlobalTheory.SW.Parab

theorem ph_rat_mul_exp (r q : ℚ) : Ph ((r : ℂ) * cexp (-(Real.pi * I * (q : ℂ)))) := by
  refine ⟨2 * q.den, by have := q.den_pos; omega, ?_⟩
  have hn : ‖cexp (-(Real.pi * I * (q : ℂ)))‖ = 1 := by
    have : -(Real.pi * I * (q : ℂ)) = ((-(Real.pi * q) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he : cexp (-(Real.pi * I * (q : ℂ))) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    have h : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
    push_cast
    rw [← h]
    ring
  rw [mul_pow, he, mul_one, norm_mul, hn, mul_one, Complex.norm_ratCast]
  have : (|(r : ℝ)|) ^ (2 * q.den) = (r : ℝ) ^ (2 * q.den) := Even.pow_abs ⟨q.den, by ring⟩ _
  rw [← Complex.ofReal_pow, this]
  push_cast
  rfl

theorem trans_explicit (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by
  classical
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hDA : D * Aᵀ = 1 := by
    have h := SymplecticGroup.mem_iff.mp hσ
    rw [← Matrix.fromBlocks_toBlocks σ, hC, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have := congrArg Matrix.toBlocks₂₁ h
    simpa using this
  have hdet : D.det * A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  refine ⟨?_, ?_⟩
  · have h1 := isSB_parChar_mul (B * Aᵀ) _
      ((GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hA0).1
    exact (GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h1 h1).2.1 _
  · intro τ _ ζ
    have hden : spDen σ τ = qm D := by
      unfold spDen
      rw [hC]
      have : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
      rw [this, Matrix.zero_mul, zero_add]
    have hinv : (qm D)⁻¹ = (qm A)ᵀ := by
      apply Matrix.inv_eq_right_inv
      have e : (qm A)ᵀ = qm Aᵀ := rfl
      rw [e, ← qm_mul', hDA]
      ext i j; by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]
    have hdetD : (qm D).det = (D.det : ℂ) := ((Rat.castHom ℂ).map_det D).symm
    have hC' : qm σ.toBlocks₂₁ = 0 := by rw [hC]; ext i j; simp [qm]
    unfold spAct
    rw [hden, hinv, hC', hdetD]
    simp only [Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one]
    let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
      { toFun := fun x => x * A
        invFun := fun x => x * A⁻¹
        left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right A x hAu
        right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right A x hAu }
    unfold thS
    rw [← tsum_mul_left, ← e.tsum_eq (fun x => _ * (φ x * _))]
    refine tsum_congr fun x => ?_
    show ((D.det : ℂ) ^ (Fintype.card κ / 2)) * (parChar (B * Aᵀ) x * φ (x * A)) * _ =
      _ * (φ (x * A) * cexp (Real.pi * I * ∑ k, (qv ((x * A) k) ⬝ᵥ τ *ᵥ qv ((x * A) k) +
        2 * (qv ((x * A) k) ⬝ᵥ ζ k))))
    rw [mul_assoc, mul_comm (parChar _ _), mul_assoc]
    congr 2
    unfold parChar
    rw [← Complex.exp_add]
    congr 1
    rw [← mul_neg, ← mul_add, Rat.cast_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qv_bilin, qv_row_mul, qm_mul']
    have e1 : qm Aᵀ = (qm A)ᵀ := rfl
    beta_reduce
    rw [e1, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec (qv (x k)) (qm A),
      Matrix.dotProduct_mulVec (qv (x k)) (qm A)]
    ring

theorem trans_unique (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e : ζ = fun k => (ζ k ᵥ* spDen σ (I • (1 : Matrix ι ι ℂ))) ᵥ*
      (spDen σ (I • (1 : Matrix ι ι ℂ)))⁻¹ := by
    funext k
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.vecMul_one]
  rw [e, h _ I_mem_siegel, h' _ I_mem_siegel]

theorem values_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  intro κ ι _ _ _ _ σ hσ hC φ ψ hφ hψ h y
  obtain ⟨h1, h2⟩ := trans_explicit κ ι σ hσ hC φ hφ
  have e := trans_unique κ ι σ hσ φ _ _ hψ h1 h h2
  refine ⟨((σ.toBlocks₂₂.det ^ (Fintype.card κ / 2) : ℚ) : ℂ) *
    parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) y, y * σ.toBlocks₁₁, ph_rat_mul_exp _ _, ?_⟩
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.Phase.ParabValues
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhaseStatement

section

@[expose] public section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  first | exact @GlobalTheory.Phase.ParabValues.values_parabolic | exact GlobalTheory.Phase.ParabValues.values_parabolic | (intros; apply GlobalTheory.Phase.ParabValues.values_parabolic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEqStatement

section

@[expose] public section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  first | exact @GlobalTheory.SW.eq_of_thS_eq | exact GlobalTheory.SW.eq_of_thS_eq | (intros; apply GlobalTheory.SW.eq_of_thS_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSUnique

section

@[expose] public section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

theorem transS_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ _ I_mem_siegel
  refine GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e1 := h _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e2 := h' _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e := e1.trans e2.symm
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.vecMul_one] using e

theorem val_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ →
      TransS (Matrix.J ι ℚ) φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ),
        Ph u ∧ ψ y = u * haar (fun x => φ x * chr y' x) := by
  intro κ ι _ _ _ ⟨p, hp⟩ φ ψ ⟨R, hR, h⟩ hψ ht y
  have e := transS_unique (SymplecticGroup.J_mem ι ℚ) hψ
    ⟨R, hR, FourierJ.ft_level hR h _⟩ ht (FourierJ.trans_J hp hR h)
  refine ⟨I ^ (Fintype.card ι * p), y, ⟨4, by norm_num, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; simp [Complex.I_pow_four]
  · rw [e]
    simp only [FourierJ.ft, FourierJ.pr, FourierJ.ech, chr]

end GlobalTheory.Phase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransform

section

@[expose] public section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.WeilPV

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem trans_unique {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (h1 : IsSB ψ) (h2 : IsSB ψ') (t1 : TransS σ φ ψ)
    (t2 : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' h1 h2 _ hs fun ζ => ?_
  have e1 := t1 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e2 := t2 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e := e1.trans e2.symm
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
    Matrix.vecMul_one] at e
  exact e


omit [DecidableEq ι] in
theorem thS_smul (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem trans_smul {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} {φ ψ : Matrix κ ι ℚ → ℂ} (c : ℂ)
    (t : TransS σ φ ψ) : TransS σ (c • φ) (c • ψ) := fun τ hτ ζ => by
  rw [thS_smul, thS_smul, t τ hτ ζ]; ring


omit [DecidableEq ι] in
theorem sb_smul (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem vac_trans {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : ∃ A ε, VacS A ε φ) :
    ∃ A ε, VacS A ε ψ := by
  obtain ⟨A, ε, h⟩ := h
  obtain ⟨T, hom, hT⟩ := GlobalTheory.Phase.transS_intertwines κ ι σ hσ
  have mem : ∀ y, y ∈ A.map T.toAddMonoidHom ↔ T.symm y ∈ A := fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun hy => ⟨_, hy, by simp⟩⟩
  have hom' : ∀ y y', om (T.symm y) (T.symm y') = om y y' := fun y y' => by
    rw [← hom]; simp
  refine ⟨A.map T.toAddMonoidHom, fun y => ε (T.symm y), ?_, ?_, ?_, ?_, ?_, hψ, ?_⟩
  · obtain ⟨S, hS⟩ := h.fg
    classical
    let e := A.equivMapOfInjective T.toAddMonoidHom T.injective
    refine ⟨S.image e, ?_⟩
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ AddSubsemigroup.closure (S : Set A) := by rw [hS]; trivial
    induction hx using AddSubsemigroup.closure_induction with
    | mem x hx =>
        apply AddSubsemigroup.subset_closure
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using AddSubsemigroup.add_mem _ (ihx (by trivial)) (ihy (by trivial))
  · intro y
    rw [mem, h.dual]
    constructor
    · intro H y' hy'
      rw [← hom']; exact H _ ((mem _).1 hy')
    · intro H y' hy'
      have := H (T y') ((mem _).2 (by simpa using hy'))
      rw [← hom'] at this
      simpa using this
  · intro y hy; exact h.norm _ ((mem _).1 hy)
  · intro y hy y' hy'
    rw [map_add (f := _), h.semi _ ((mem _).1 hy) _ ((mem _).1 hy'), hom']
  · obtain ⟨m, hm, H⟩ := h.ord
    exact ⟨m, hm, fun y hy => by rw [map_nsmul]; exact H _ ((mem _).1 hy)⟩
  · intro y hy
    have t1 := trans_smul (ε (T.symm y)) (hT φ ψ h.sb hψ t (T.symm y))
    rw [h.fix _ ((mem _).1 hy), T.apply_symm_apply] at t1
    exact trans_unique hσ (sb_smul _ (GlobalTheory.SW.heisS_laws _ _ _ _ ψ hψ).1) hψ t1 t


omit [DecidableEq ι] in
theorem pv_sb {φ : Matrix κ ι ℚ → ℂ} (h : PV φ) : IsSB φ := by
  obtain ⟨⟨_, _, h⟩, -⟩ := h
  exact h.sb

theorem pv_parabolic (he : Even (Fintype.card κ)) {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (h0 : σ.toBlocks₂₁ = 0)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans hσ hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity κ ι he σ hσ h0 φ ψ (pv_sb h) hψ t y
  rw [e]; exact hu.mul (h.2 _)

theorem pv_J (he : Even (Fintype.card κ))
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS (Matrix.J ι ℚ) φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans (SymplecticGroup.J_mem ι ℚ) hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.Phase.val_trans_J κ ι he φ ψ (pv_sb h) hψ t y
  rw [e]
  exact hu.mul (GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase κ ι _
    ((GlobalTheory.Phase.shape_conj_chr_mul κ ι φ ((GlobalTheory.Phase.VacShape.vacuum_shape κ ι φ).2.1 h)).2.1 y'))

theorem pv_mul (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by
  intro φ ψ hψ t h
  obtain ⟨w, hw⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ he hσ
  obtain ⟨w', hw'⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ' he hσ'
  obtain ⟨s1, t1, -⟩ := hw φ (pv_sb h)
  obtain ⟨s2, t2, -⟩ := hw' (w φ) s1
  have t3 := GlobalTheory.SW.transS_comp κ ι σ σ' hσ hσ' _ _ _ t1 t2
  rw [trans_unique (mul_mem hσ' hσ) hψ s2 t t3]
  exact H' _ _ s2 t2 (H _ _ s1 t1 h)

theorem pv_of_transS : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  intro κ ι _ _ _ he σ hσ
  obtain ⟨p₁, h1, p₂, h2, p₃, h3, z1, z2, z3, rfl⟩ :=
    GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ := SymplecticGroup.J_mem ι ℚ
  have P : ∀ p ∈ Matrix.symplecticGroup ι ℚ, p.toBlocks₂₁ = 0 →
      ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS p φ ψ → PV φ → PV ψ :=
    fun p hp z φ ψ hψ t h => pv_parabolic he hp z hψ t h
  have Q : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (Matrix.J ι ℚ) φ ψ → PV φ → PV ψ :=
    fun φ ψ hψ t h => pv_J he hψ t h
  have a := mul_mem h1 hJ
  have b := mul_mem a h2
  have c := mul_mem b hJ
  exact pv_mul he h3 c (P _ h3 z3) (pv_mul he hJ b Q (pv_mul he h2 a (P _ h2 z2)
    (pv_mul he hJ h1 Q (P _ h1 z1))))

end GlobalTheory.Phase.WeilPV
end
end
