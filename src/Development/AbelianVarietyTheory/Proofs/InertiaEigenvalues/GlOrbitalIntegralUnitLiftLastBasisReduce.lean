module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
public import Mathlib.Analysis.Normed.Group.Ultra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLSStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionIStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasisStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrandStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  first | exact @GlobalTheory.JR.orbG_integrand_hasCompactSupport | exact GlobalTheory.JR.orbG_integrand_hasCompactSupport | (intros; apply GlobalTheory.JR.orbG_integrand_hasCompactSupport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompact

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLift

theorem glO_isOpen_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  intro F _ _ _ n
  let B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : F) 1))
  have hB : ∀ A : Matrix (Fin n) (Fin n) F, A ∈ B ↔ ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A
    constructor
    · intro h i j
      have := h i (Set.mem_univ _) j (Set.mem_univ _)
      simpa using this
    · intro h i _ j _
      simpa using h i j
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix (Fin n) (Fin n) F × (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ) :=
    B ×ˢ (MulOpposite.unop ⁻¹' B)
  have hS : glO n F = Units.embedProduct _ ⁻¹' S := by
    ext g
    simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, S, Set.mem_prod, hB, Units.embedProduct_apply,
      MulOpposite.unop_op]
    constructor
    · intro h; exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
    · intro h i j; exact ⟨h.1 i j, h.2 i j⟩
  have hSo : IsOpen S := hBo.prod (hBo.preimage MulOpposite.continuous_unop)
  have hSc : IsCompact S := by
    refine hBc.prod ?_
    have : MulOpposite.unop ⁻¹' B = MulOpposite.op '' B := by
      ext x
      constructor
      · intro h; exact ⟨_, h, MulOpposite.op_unop x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]; exact hBc.image MulOpposite.continuous_op
  rw [hS]
  exact ⟨hSo.preimage Units.continuous_embedProduct,
    Units.isClosedEmbedding_embedProduct.isCompact_preimage hSc⟩

end GlobalTheory.JR.GLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompactStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Step.EmbClosed

theorem embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

theorem continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _

theorem isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)

theorem isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by
  have hE := isClosedEmbedding_embHom r F
  let Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ :=
    Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)
  have hΦ : IsClosedEmbedding Φ := by
    refine hE.prodMap ?_
    exact MulOpposite.opHomeomorph.isClosedEmbedding.comp
      (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _ := by
    funext g
    rfl
  rw [← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]
  exact hΦ.comp Units.isClosedEmbedding_embedProduct

end GlobalTheory.JR.Step.EmbClosed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbeddingStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugation

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OmegaInv

theorem norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

theorem eta_congr {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto

theorem omega_act (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ)
    (k : GL (Fin n) F) (hk : k ∈ glO n F) (Y : Gl n F) : omega (act k Y) = omega Y := by
  unfold omega
  apply eta_congr
  have h1 := (GlobalTheory.JR.transfer_factor_lemma F n).1
  have h2 := (GlobalTheory.JR.transfer_factor_lemma F n).2
  have hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    rw [h1, h1, h2, Matrix.det_mul, mul_assoc]
  have ha := norm_det_le_one _ (fun i j => (hk i j).1)
  have hb := norm_det_le_one _ (fun i j => (hk i j).2)
  have hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    apply le_antisymm hb
    by_contra hlt
    push_neg at hlt
    have : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
    linarith
  rw [hl, norm_mul, hkinv, mul_one]

end GlobalTheory.JR.OmegaInv

theorem GlobalTheory.JR.omega_act_glO : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y :=
  fun F _ _ n k hk Y => GlobalTheory.JR.OmegaInv.omega_act F n k hk Y
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugationStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by
  first | exact @GlobalTheory.JR.omega_act_glO | exact GlobalTheory.JR.omega_act_glO | (intros; apply GlobalTheory.JR.omega_act_glO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduce

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := GlobalTheory.T.integralGLSet_isOpen_and_isCompact F (r + 1)
  have hemb := GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral F (r + 1) k hk, GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral F (r + 1) k hk])
    (fun g hg => GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix, GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
end
end
end
