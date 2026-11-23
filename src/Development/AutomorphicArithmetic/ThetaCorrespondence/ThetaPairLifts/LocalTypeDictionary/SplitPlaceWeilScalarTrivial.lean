module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentConjugateToSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ParabolicDerivativeFixesSplitVector
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ParabolicDerivativeFixesSplitVector

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertDbl.inlD_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  apply GlobalTheory.InertBigCell.inlD_mem <;> assumption
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  first | exact @GlobalTheory.InertDbl.inlD_mem_KAtD | exact GlobalTheory.InertDbl.inlD_mem_KAtD | (intros; apply GlobalTheory.InertDbl.inlD_mem_KAtD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
open GlobalTheory.SplitDblGen

namespace GlobalTheory.SplitDblGen

theorem inlD_mem_closure_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp _ h2 k hk
  obtain ⟨c, hcσ, hcAt, hc2, hcL⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hTr.base v hsp
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ _ G.W v h2 c hcσ hcAt (hcL _ G.W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ _ G.W v h2 c hcσ (hcL _ G.W) k hk
  have hg := GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer F E σ _ G.W v k hk
  have hKK' : mat k * mat k⁻¹ = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (mul_inv_cancel k)
  have hK'K : mat k⁻¹ * mat k = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (inv_mul_cancel k)
  have hAtK : At (evFin F v) (mat k - 1) := hk.1
  have hAtK' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [Matrix.mul_sub, hK'K, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hAtK u hu, Matrix.mul_zero, neg_zero]
  have hc2M : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), At (evFin F v) M → (c * c) • M = M := by
    intro M hM
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc2 _ (fun u hu => by
      have h0 := congrFun (congrFun (hM u hu) i) j
      simpa using h0)
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k) (mat k⁻¹) hKK' (hc2M _ hAtK)
  have ht' := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k⁻¹) (mat k) hK'K (hc2M _ hAtK')
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E _ c (mat k) (mat k⁻¹) hKK' hK'K (hc2M _ hAtK)
  let T : GL (Fin (a + a')) (AE F E) := ⟨tMat c (mat k), tMat c (mat k⁻¹), ht, ht'⟩
  have hinv : GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD n = 1 := GlobalTheory.DblVacFlip.matD_inv_mul n
  have hq : n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k ∈ GlobalTheory.InertDbl.ParD σ G.W v := by
    refine ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.inv_mem_KD hn.1) hp.1) hg, T, ?_⟩
    show GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD p * GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ G.W k) *
        diagCols (Fin (a + a')) = diagCols (Fin (a + a')) * tMat c (mat k)
    have h3 := congrArg (fun M => GlobalTheory.InertDbl.matD n⁻¹ * M) hid
    simp only [← Matrix.mul_assoc] at h3
    rw [GlobalTheory.InertDbl.matD_inlD, hpm]
    refine h3.trans ?_
    rw [← hnm, hinv]
    exact congrArg (· * tMat c (mat k)) (Matrix.one_mul _)
  have e : GlobalTheory.InertDbl.inlD σ G.W k = p⁻¹ * n * (n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k) := by group
  rw [e]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (s _ (Or.inl hp))) (s _ (Or.inr hn))) (s _ (Or.inl hq))

end GlobalTheory.SplitDblGen

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.scalarSq_smul_matrix_supported_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  first | exact @GlobalTheory.SplitDblGen.inlD_mem_closure_split | exact GlobalTheory.SplitDblGen.inlD_mem_closure_split | (intros; apply GlobalTheory.SplitDblGen.inlD_mem_closure_split <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DoubleVacuumLineEigenspaceSplit

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.DblVacLineSplit
theorem doubleLine_eigenfunction_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ hunr _ _ dd omd hdd hS R _ hR g hg
  exact GlobalTheory.DblVacLine.dbl_line hT.base.std v hunr hT.geo.hV'.lat.toIsLattice hT.geo.hW.lat.toIsLattice
    (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v)
    G.M' _ (hT.geo.hM'.vac v) dd omd hdd hS.2.1 R hR g hg
end GlobalTheory.DblVacLineSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubleVacuum_line_eigenspace_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.DblVacLineSplit.doubleLine_eigenfunction_split | exact _root_.GlobalTheory.DblVacLineSplit.doubleLine_eigenfunction_split | (intros; apply _root_.GlobalTheory.DblVacLineSplit.doubleLine_eigenfunction_split <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GradientFixesSplitVector

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.NabFixSplit
theorem gradient_fixes_split_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  have hLine := _root_.GlobalTheory.T.doubleVacuum_line_eigenspace_split
  have hConj := GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv n hn
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  obtain ⟨c, hc⟩ := hLine hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv n hn.1
  obtain ⟨s, hs, hsn⟩ := hConj F E σ B hTr.base (a + a') G.W v hsp h2 n hn
  have hs1 : omd s Φ = Φ := _root_.GlobalTheory.T.split_double_parabolic_derivative_fixed hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv s hs
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    rw [map_mul, Module.End.mul_apply, hc, map_smul, hc, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hc, h0, zero_smul, map_zero]
  · rw [hc, h1, one_smul]
end GlobalTheory.NabFixSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.nabla_preserves_split_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.NabFixSplit.gradient_fixes_split_vector | exact _root_.GlobalTheory.NabFixSplit.gradient_fixes_split_vector | (intros; apply _root_.GlobalTheory.NabFixSplit.gradient_fixes_split_vector <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitPlaceWeilScalarTrivial

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitScalar
theorem weil_scalar_eq_one_of_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨-, dd, omd, hdc, hws, hres⟩ := hTr.weil'.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.W) :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.scalarSq_smul_matrix_supported_at_place) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (_root_.GlobalTheory.T.split_double_parabolic_derivative_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
    · exact (_root_.GlobalTheory.T.nabla_preserves_split_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (1, k) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'
end GlobalTheory.SplitScalar
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.split_place_weil_scalar_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | exact _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split | (intros; apply _root_.GlobalTheory.SplitScalar.weil_scalar_eq_one_of_split <;> assumption)
end
end
end
