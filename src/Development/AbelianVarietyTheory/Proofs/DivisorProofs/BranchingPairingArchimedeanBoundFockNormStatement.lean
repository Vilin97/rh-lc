module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledCoisometryNorms
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingMapExtendScalarsEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFockNormAdjugateSubstSymmLeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinearFockPairingSqLeHermitianNorms

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.FockCauchySchwarz

variable {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m)

theorem pairK_one (x y : VV ℂ w) :
    pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y = pairBK w (GlobalTheory.BranchNorm.cV w x) y := by
  have h := GlobalTheory.BranchNorm.pairK_eq w (1 : ι → GL (Fin m) ℂ) x y
  rw [map_one] at h
  exact h

theorem pairK_cs (x y : VV ℂ w) :
    ‖pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y‖ ^ 2 ≤
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
        (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  have hG : ∀ _ : ι, (1 : Matrix (Fin m) (Fin m) ℂ).PosDef := fun _ => Matrix.PosDef.one
  rw [← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (GlobalTheory.CoefModel.toHilb w hG x) (GlobalTheory.CoefModel.toHilb w hG y)
  rw [norm_inner_symm (GlobalTheory.CoefModel.toHilb w hG y), ← sq] at h
  exact h

theorem pairBK_sq_le : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  intro ι _ m w x y
  have h := pairK_cs w (GlobalTheory.BranchNorm.cV w x) y
  rw [pairK_one, pairK_one w (GlobalTheory.BranchNorm.cV w x), GlobalTheory.BranchNorm.cV_cV] at h
  rw [pairK_one w x x, pairBK_apply w (GlobalTheory.BranchNorm.cV w x), pairingBSymm_holds, ← pairBK_apply]
  exact h

end GlobalTheory.FockCauchySchwarz
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinearFockPairingSqLeHermitianNormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  first | exact @GlobalTheory.FockCauchySchwarz.pairBK_sq_le | exact GlobalTheory.FockCauchySchwarz.pairBK_sq_le | (intros; apply GlobalTheory.FockCauchySchwarz.pairBK_sq_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBounds

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BranchNormBound

open GlobalTheory.BranchFormula GlobalTheory.BranchNorm GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

theorem const_le {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (hI : Interlace rfl lam sg) (hS : SameShift lam sg) :
    ((cBr rfl lam sg : ℤ) : ℝ) ^ 2 * kapBr ℝ rfl lam sg ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 := by
  have hx : xiBr ℂ rfl lam sg ∈ delSq ℂ (n + 1) lam := nablaSq_eq_delSq ℂ lam ▸ xi_mem hI hS
  have h := (onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs (n + 1) n rfl lam sg hI hS).2.2.2.2.2 _ hx
  have hk : normFock lam (xiBr ℂ rfl lam sg) (xiBr ℂ rfl lam sg) = kapBr ℂ rfl lam sg := by
    rw [kapBr, normFock, fockF_eq, fockF_eq, GlobalTheory.Proof.TensorMapDescent.xiBr_map, Formalism.L2.DIV.map_extremal]
  have e1 : ((kapBr ℝ rfl lam sg : ℝ) : ℂ) = kapBr ℂ rfl lam sg := kapBr_map Complex.ofRealHom
  obtain ⟨s1, -⟩ := fockF_self_ne (f := extremal ℂ n sg) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl sg.natW)
  have h5 : normFock sg (extremal ℂ n sg) (extremal ℂ n sg) = 1 := div_self s1
  rw [brOne_xi rfl hI hS, normFock_smul, h5, hk, ← e1] at h
  simp only [map_mul, map_intCast, Complex.conj_ofReal, mul_one, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  have hp := kapBr_pos hI hS
  refine le_of_mul_le_mul_right ?_ hp
  nlinarith

theorem sumGram_one (n : ℕ) : sumGram (n + 1) (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  ext a b
  have := a.2
  have := b.2
  simp only [sumGram, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem brStd_norm_le {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (hI : ∀ τ, Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, SameShift (Λ τ) (σ τ)) (x : VV ℂ Λ) :
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (brStd hN Λ σ x) (brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
        (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  subst hN
  have h1 : ∀ m : ℕ, ((1 : Matrix (Fin m) (Fin m) ℂ).map (RingHom.id ℂ)).PosDef := fun m => by
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef)
  have h := (brNorm ℂ (RingHom.id ℂ) (fun _ => rfl) ι (n + 1) n rfl Λ σ hI hS (fun _ => 1) (fun _ => h1 n)
    (fun _ => 1) (fun _ => 1) 1 one_pos (fun _ => by simp)).2.2.1 x
  simp only [nrmSq, sumGram_one, brAt, one_zpow, Finset.prod_const_one, one_smul, RingHom.id_apply, brSq, one_mul] at h
  have hp := pairK_pos (RingHom.id ℂ) (fun _ => rfl) Λ (G := fun _ => 1) (fun _ => h1 _) x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (sq_nonneg _) (kapBr_pos (hI τ) (hS τ)).le)
    fun τ _ => const_le (hI τ) (hS τ)

end GlobalTheory.BranchNormBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBoundsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds : ∀ {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ (x : VV ℂ Λ),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (Formalism.L2.Col.Br.brStd hN Λ σ x) (Formalism.L2.Col.Br.brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) * (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  first | exact @GlobalTheory.BranchNormBound.brStd_norm_le | exact GlobalTheory.BranchNormBound.brStd_norm_le | (intros; apply GlobalTheory.BranchNormBound.brStd_norm_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNorm

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BrPairBound

theorem pairK_one_re_nonneg {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x : VV ℂ w) :
    0 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re := by
  by_cases h : x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w (G := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun _ => Matrix.PosDef.one) x h)).1.le

theorem inf_bound : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  intro K ι _ _ _ φ n N hN Λ σ hI hS u v
  refine ⟨pairK_one_re_nonneg _ _, pairK_one_re_nonneg _ _, ?_⟩
  rw [GlobalTheory.T.branchingPairing_map_extendScalars_embedding φ hN Λ σ u v, GlobalTheory.BrPairF.brPairF_apply]
  set u' := GlobalTheory.CoefModel.mapVV φ Λ u
  set v' := GlobalTheory.CoefModel.mapVV φ _ v
  have h1 := GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms σ (Formalism.L2.Col.Br.brStd hN Λ σ u') ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have h2 := GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds hN Λ σ hI hS u'
  have h3 := GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le σ v'
  have p2 := pairK_one_re_nonneg σ ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have p3 := pairK_one_re_nonneg Λ u'
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul h2 h3 p2 (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) p3)
    _ = _ := by ring

end GlobalTheory.BrPairBound

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNormStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  first | exact @GlobalTheory.BrPairBound.inf_bound | exact GlobalTheory.BrPairBound.inf_bound | (intros; apply GlobalTheory.BrPairBound.inf_bound <;> assumption)
end
end
