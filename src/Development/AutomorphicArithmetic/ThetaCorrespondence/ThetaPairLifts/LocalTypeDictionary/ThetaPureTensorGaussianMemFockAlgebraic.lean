module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianThetaImagesAlgebraic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaGaussAlg

variable {D : D7}

theorem fockF_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    (f : WO M X → ℂ) : fockF ψ θ ε A B f 1 = f := by
  simp only [fockF, pureTensorO, pureTensorL]
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank M.rank) ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem det_gram_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hb : ∀ i, V.hT (V.frame i) (∑ j, v j • V.frame j) = 0 := by
    intro i
    have hi : V.hT (V.frame i) (∑ j, v j • V.frame j) = (V.gram *ᵥ v) i := by

      simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hi, hv]
    rfl
  have hy : (∑ j, v j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun x => ?_

    rw [← V.frame.sum_repr x, map_sum V.hT, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  exact hv0 (funext (Fintype.linearIndependent_iff.mp V.frame.linearIndependent v hy))

theorem incM_gram_inv (S : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram = 1 := by
  have hu : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero S)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

def crd (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) : Matrix (Fin S.rank) (Fin k) (AE D) ≃+ WO S X where
  toFun u := (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D))
  invFun x := GlobalTheory.TripleRead.ptO S.gram e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, (incM_gram_inv S).1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have : (GlobalTheory.TripleRead.ptO S.gram e x)ᵀ.submatrix e.symm id =
        (HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [this]
    rw [Matrix.mul_assoc, (incM_gram_inv S).2, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.ThetaGaussAlg

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPureTensorGaussianMemFockAlgebraic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaGaussAlg
variable {D : D7}
theorem theta_pure_tensor_gaussian_mem_fockAlgebraic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
          GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ algF ψ θ false A₁ B := by
  intro _ _ D ψ θ _ hθ W W₁ X A A₁ B α β _ ωA ωB _ _ e Bs Γ Xc om om' h _ _ R Rf hM f₀ φ hg hφ hvac
  obtain ⟨f, hf, hD⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ false W₁ X A₁ B e.symm Bs hM.triple.base h.ψ Γ.V' Γ.W _ _ _ _
    (by simpa using h.JW₁) h.JX hM.triple.geo.hV' hM.triple.geo.hW
    (fun w => by
      obtain ⟨τ, h1, -, h3, h4⟩ := h.cart w
      exact ⟨τ, h1, by simpa using h3, h4⟩)
    Γ.M' hM.triple.geo.hM' (crd W₁ X e) (fun u => by simp only [Bool.false_eq_true, if_false, one_smul]; rfl)
    f₀ φ hg hφ hvac
  have e1 : GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
    funext x
    exact (hD.2 ((crd W₁ X e).symm x)).trans (congrArg f ((crd W₁ X e).apply_symm_apply x))
  rw [e1]
  exact Submodule.subset_span ⟨f, 1, hf, (fockF_one ψ θ false A₁ B f).symm⟩
end GlobalTheory.ThetaGaussAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.pure_gaussian_theta_lift_algebraic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
          GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ algF ψ θ false A₁ B := by
  first | exact @_root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic | exact _root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic | (intros; apply _root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic <;> assumption)
end
end
end
