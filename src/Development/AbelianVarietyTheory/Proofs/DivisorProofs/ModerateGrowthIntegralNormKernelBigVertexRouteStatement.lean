module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernelStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLtStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank | exact GlobalTheory.FunObj.squareTriple_sig_rank | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMul

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace CompanionTheory.Member.BlockMatrixNorms

theorem sq_le {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (x : n → ℂ) :
    ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  exact h2

theorem opNorm_blk {m n ι : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : m ⊕ n ≃ ι) (x : Matrix m m ℂ) (y : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y)‖₊ ≤
      max ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖₊ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖₊ := by
  rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_nnnorm, coe_nnnorm, coe_nnnorm]
  set a := ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖ with ha
  set b := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hm : 0 ≤ max a b := le_max_of_le_left ha0
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun w => ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hm (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h1 := sq_le x (fun i => w.ofLp (e (.inl i)))
  have h2 := sq_le y (fun i => w.ofLp (e (.inr i)))
  have e1 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inl i)) =
      (x *ᵥ fun i => w.ofLp (e (.inl i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inl i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  have e2 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inr i)) =
      (y *ᵥ fun i => w.ofLp (e (.inr i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inr i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  rw [← e.sum_comp, ← e.sum_comp (fun i => ‖w.ofLp i‖ ^ 2), Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [e1, e2]
  have s1 : 0 ≤ ∑ i, ‖w.ofLp (e (.inl i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have s2 : 0 ≤ ∑ i, ‖w.ofLp (e (.inr i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have p1 : a ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ ha0 (le_max_left _ _) 2
  have p2 : b ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ hb0 (le_max_right _ _) 2
  rw [mul_add]
  exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right p1 s1)) (h2.trans (mul_le_mul_of_nonneg_right p2 s2))

theorem key {c c' a a' b b' : NNReal} (h : c ≤ max a b) (h' : c' ≤ max a' b') :
    max 1 (max c c') ≤ max 1 (max a a') * max 1 (max b b') := by
  have hA : 1 ≤ max 1 (max a a') := le_max_left _ _
  have hB : 1 ≤ max 1 (max b b') := le_max_left _ _
  have l1 : max 1 (max a a') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_right' hB
  have l2 : max 1 (max b b') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_left' hA
  refine max_le (hA.trans l1) (max_le (h.trans (max_le ?_ ?_)) (h'.trans (max_le ?_ ?_)))
  · exact (le_max_of_le_right (le_max_left _ _)).trans l1
  · exact (le_max_of_le_right (le_max_left _ _)).trans l2
  · exact (le_max_of_le_right (le_max_right _ _)).trans l1
  · exact (le_max_of_le_right (le_max_right _ _)).trans l2

theorem sup_blk {A m n ι κ : Type} [CommRing A] [Fintype m] [Fintype n] [Fintype ι] [Fintype κ]
    (e : m ⊕ n ≃ ι) (φ : A → κ → NNReal) (hφ : ∀ k, φ 0 k = 0) (x : Matrix m m A) (y : Matrix n n A) :
    (Finset.univ.sup fun p : ι × ι × κ => φ (GlobalTheory.Doubling.blkMat e x y p.1 p.2.1) p.2.2) ≤
      max (Finset.univ.sup fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2)
        (Finset.univ.sup fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) := by
  refine Finset.sup_le ?_
  rintro ⟨i, j, k⟩ -
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [GlobalTheory.Doubling.blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · exact le_max_of_le_left (Finset.le_sup (f := fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))
  · simp [hφ]
  · simp [hφ]
  · exact le_max_of_le_right (Finset.le_sup (f := fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))

variable {D : D7}

theorem finMat_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    finMat D.sp.cm.sig (hsum V V₁).gram (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (finMat D.sp.cm.sig V.gram g) (finMat D.sp.cm.sig V₁.gram g₁) :=
  blkMat_map finSumFinEquiv _ (map_zero _) (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)

theorem infMat_blk (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    infMat D.sp.cm.sig (hsum V V₁).gram θ (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (infMat D.sp.cm.sig V.gram θ g) (infMat D.sp.cm.sig V₁.gram θ g₁) := by
  have h := blkMat_map finSumFinEquiv
    (fun z => θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z)) (by simp only [map_zero])
    (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)
  exact h

theorem infNorm_blk (θ : InfFam D) (V V₁ : HSp D) (τ : D.what₂.Tau) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ (hsum V V₁) τ (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V₁ τ g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm
  rw [infMat_blk]
  exact opNorm_blk _ _ _

theorem finNorm_blk (V V₁ : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm (hsum V V₁) v (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V v g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V₁ v g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  rw [finMat_blk]
  refine sup_blk finSumFinEquiv (fun z k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D z k)‖₊) (fun k => ?_) _ _
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k = 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord
    rw [map_zero]; rfl
  show ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k)‖₊ = 0
  rw [hz, map_zero, nnnorm_zero]

theorem blk_inv (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    (blk V V₁ (g, g₁))⁻¹ = blk V V₁ (g⁻¹, g₁⁻¹) := (map_inv (blk V V₁) (g, g₁)).symm

end CompanionTheory.Member.BlockMatrixNorms

theorem CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  intro D θ V V₁ g g₁
  have f0 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite (hsum V V₁) (blk V V₁ (g, g₁))
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V₁ g₁
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib f1 f2]
  refine mul_le_mul' (Finset.prod_le_prod' fun τ _ => ?_) ?_
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
  · refine finprod_le_finprod' f0 ((f1.union f2).subset (Function.mulSupport_mul _ _)) fun v => ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | exact CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | (intros; apply CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul <;> assumption)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | exact GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | (intros; apply GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRoute

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRoute

theorem modGrowth_integral_norm_kerBig {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) :
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  obtain ⟨ε, ω, χ, χ', Φ, C₀, hω, hΦ, hb⟩ := GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel (G := G) hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt W t i j hT M hM
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨N, Cw, hMI⟩ := hWC D W.ψ W.θ W.θ_is ε _ _ χ χ' ω hω p hsig hrk _ _ hHF Φ hΦ
  obtain ⟨Cc, hCc, hcmp⟩ := GlobalTheory.Grow.height_comparison (G.V (.grid i (j + 1))) W.θ_is
  set h₁ : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g₁ : ℝ)
  refine ⟨max C₀ 0 * (max Cw 0 * (Cc * h₁) ^ N), N, fun g => ?_⟩
  have hI := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).1
  have hle := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).2
  have hpos : 0 ≤ ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hpos]
  have h1 : ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) ≤
      ∫ u in M.fd (.grid (i + 1) (j + 1)), max C₀ 0 * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hI.norm.const_mul _)
      (Filter.Eventually.of_forall fun u => (hb g u).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  rw [integral_const_mul] at h1
  have hX := GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul D W.θ _ _ g g₁
  have hXg : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ≤
      Cc * GlobalTheory.Grow.height _ g * h₁ := by
    have := (hcmp g).1
    calc _ ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g : ℝ) * h₁ := by exact_mod_cast hX
      _ ≤ _ := mul_le_mul_of_nonneg_right this (NNReal.coe_nonneg _)
  have h0 : (0 : ℝ) ≤ ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have h2 : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      (Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 (hXg.trans_eq (by ring)) N
  have h3 : Cw * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 _)).trans
      (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
  calc _ ≤ _ := h1
    _ ≤ max C₀ 0 * (max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N)) :=
      mul_le_mul_of_nonneg_left (hle.trans h3) (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.BigRoute
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRouteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  first | exact @GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig | exact GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig | (intros; apply GlobalTheory.BigRoute.modGrowth_integral_norm_kerBig <;> assumption)
end
end
