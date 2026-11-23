module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemannStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.InnerProductSpace.Calculus

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormFockMatrixEqNegSumImRealPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockOmega

variable {D : D7}

open GlobalTheory.FockTransport

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem jm_eq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = Matrix.diagonal fun a => ((sg (ε a) : ℝ) : ℂ) := by
  rw [Formalism.REAL.Jm]
  congr 1
  funext a
  cases ε a <;> simp [sg]

theorem gramAt_inv {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) :
    (gramAt D V τ)⁻¹ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ := by
  have hP := det_fr_unit A τ
  rw [← A.fr_gram τ]
  apply Matrix.inv_eq_left_inv
  have h1 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.conjTranspose_one]
  calc (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
      = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [jm_mul_self, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem hAt_frame {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ ((B.fr τ)⁻¹ * X * A.fr τ) ((B.fr τ)⁻¹ * Y * A.fr τ) =
      (Formalism.REAL.Jm (A.ε τ) * (Yᴴ * (Formalism.REAL.Jm (B.ε τ) * X))).trace := by
  have hA := det_fr_unit A τ
  have hB := det_fr_unit B τ
  have cA : ∀ M : Matrix (Fin S.rank) (Fin S.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have cB : ∀ M : Matrix (Fin T.rank) (Fin S.rank) ℂ, ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hB, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [GlobalTheory.VacUnique.hAt, gramAt_inv A τ, ← B.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, cA, cB, Matrix.mul_nonsing_inv_cancel_left _ _ hB]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA]

theorem trace_jm {m n : ℕ} (a : Fin n → Bool) (b : Fin m → Bool) (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (Formalism.REAL.Jm a * (Yᴴ * (Formalism.REAL.Jm b * X))).trace =
      ∑ i, ∑ j, ((sg (a j) : ℝ) : ℂ) * (conj (Y i j) * (((sg (b i) : ℝ) : ℂ) * X i j)) := by
  rw [Finset.sum_comm]
  simp only [jm_eq, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, Matrix.conjTranspose_apply, RCLike.star_def]

theorem term_re (b a : Bool) (ξ z y : ℂ) (hξ : ξ.re = 0) :
    2 * (ξ * (((sg a : ℝ) : ℂ) * (conj (cf b a y) * (((sg b : ℝ) : ℂ) * cf b a z)))).re =
      -(2 * (ξ.im * (z * conj y).im)) := by
  cases a <;> cases b <;> simp [cf, sg, Complex.mul_re, Complex.mul_im, hξ] <;> ring_nf <;> simp

theorem omO_fockMat (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (Z Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S)
      (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) =
      -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  refine (GlobalTheory.VacUnique.omO_apply S T _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show GlobalTheory.VacUnique.omAt S T τ (fockMat A B τ (Z τ)) (fockMat A B τ (Y τ)) = _
  rw [GlobalTheory.VacUnique.omAt, fockMat_eq, fockMat_eq, hAt_frame, trace_jm, Formalism.IndefR.Fock.CCR.norm_embedding_hostFormConstant_eq]
  simp only [Finset.mul_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  exact term_re _ _ _ _ _ (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ)

end GlobalTheory.FockOmega
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormFockMatrixEqNegSumImRealPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (Z Y : VCx D.what₂.Tau S.rank T.rank), GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S) (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) = -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  first | exact @GlobalTheory.FockOmega.omO_fockMat | exact GlobalTheory.FockOmega.omO_fockMat | (intros; apply GlobalTheory.FockOmega.omO_fockMat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiable

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section
namespace GlobalTheory.FockEntire
open GlobalTheory.FockCompare

theorem gauss_w_cr {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) :
    Differentiable ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) ∧
    ∀ Z Y : VCx ι a b, fderiv ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) Z (Complex.I • Y) =
      (∑ τ, ∑ i, ∑ j, (c τ : ℂ) * Z τ i j * conj (Y τ i j)) * ((Real.exp (gq c Z / 2) : ℝ) : ℂ) := by
  let P : ι → Fin b → Fin a → (VCx ι a b →L[ℝ] ℂ) := fun τ i j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => Fin a → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin b → Fin a → ℂ) τ))
  have hP : ∀ τ i j (Z : VCx ι a b), P τ i j Z = Z τ i j := fun _ _ _ _ => rfl
  have hq : ∀ Z : VCx ι a b, HasFDerivAt (fun Z : VCx ι a b => gq c Z / 2)
      ((1 / 2 : ℝ) • ∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)) Z := fun Z => by
    have h : HasFDerivAt (fun Z : VCx ι a b => gq c Z)
        (∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)) Z := by
      unfold gq
      refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
      exact ((P τ i j).hasFDerivAt.norm_sq).const_smul (c τ)
    have e : (fun Z : VCx ι a b => gq c Z / 2) = fun Z => (1 / 2 : ℝ) • gq c Z := by
      funext Z; rw [smul_eq_mul]; ring
    rw [e]
    exact h.const_smul (1 / 2 : ℝ)
  have hE : ∀ Z : VCx ι a b, HasFDerivAt (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (Real.exp (gq c Z / 2) •
        ((1 / 2 : ℝ) • ∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)))) Z :=
    fun Z => Complex.ofRealCLM.hasFDerivAt.comp Z (hq Z).exp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  have key2 : ∀ (r : ℝ) (z y : ℂ), (r : ℂ) * z * starRingEnd ℂ y =
      (r : ℂ) * (((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ)) := by
    intro r z y; rw [mul_assoc, key]
  simp_rw [key2]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {D : D7}

theorem cplxO_smulC {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem jO_fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.jO S T A.cart B.cart (fun τ => fockMat A B τ (Y τ) : RW T S) =
      (fun τ => fockMat A B τ ((Complex.I • Y) τ) : RW T S) := by
  funext τ
  show cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (Y τ)) = fockMat A B τ ((Complex.I • Y) τ)
  unfold fockMat
  rw [cplxO_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC, cplxO_smulC, GlobalTheory.FockCreaDir.cplxO_unitMap_fr, cplxO_smulC,
    GlobalTheory.FockCreaDir.cplxO_unitMap_fr]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, smul_smul]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def fockLin {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) :
    VCx D.what₂.Tau S.rank T.rank →ₗ[ℝ] RW T S where
  toFun z := (fun τ => fockMat A B τ (z τ) : RW T S)
  map_add' z w := by
    funext τ
    show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
    simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    abel
  map_smul' c z := by
    funext τ
    show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
    simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
      mul_smul, Finset.smul_sum, smul_add]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.coe_smul]

theorem rd_differentiable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D),
    IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ x, Differentiable ℂ (rd ψ σ A B f x) := by
  intro D ψ θ σ hψ h S T A B f hf x
  let M : VCx D.what₂.Tau S.rank T.rank →L[ℝ] RW T S := LinearMap.toContinuousLinearMap (fockLin A B)
  have hM : ∀ Z, M Z = (fun τ => fockMat A B τ (Z τ) : RW T S) := fun Z => rfl
  set G : RW T S → ℂ := fun w => heisO ψ S T (iotaW σ T S w) f x with hG
  set E : VCx D.what₂.Tau S.rank T.rank → ℂ := fun Z => ((Real.exp (gq (fw D) Z / 2) : ℝ) : ℂ) with hE
  obtain ⟨hGd, hGc⟩ := GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann D θ σ h ψ hψ S T A B f hf x
  obtain ⟨hEd, hEc⟩ := gauss_w_cr (a := S.rank) (b := T.rank) (fw D)
  have hrd : rd ψ σ A B f x = fun Z => G (M Z) * E Z := by
    funext Z
    show _ * _ = _
    rw [mul_comm]
    rfl
  rw [hrd]
  have hd : ∀ Z Y, fderiv ℝ (fun Z => G (M Z)) Z Y = fderiv ℝ G (M Z) (M Y) := fun Z Y => by
    have h1 : HasFDerivAt (fun Z => G (M Z)) ((fderiv ℝ G (M Z)).comp M) Z :=
      (hGd (M Z)).hasFDerivAt.comp Z M.hasFDerivAt
    rw [h1.fderiv]
    rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => G (M Z)) E
    (fun Z Y => ∑ τ, ∑ i, ∑ j, (fw D τ : ℂ) * Z τ i j * conj (Y τ i j))
    (hGd.comp M.differentiable) hEd (fun Z Y => ?_) hEc
  rw [hd, hd]
  have hJ : M (Complex.I • Y) = GlobalTheory.VacUnique.jO S T A.cart B.cart (M Y) := by
    rw [hM, hM, jO_fockMat]
  rw [hJ, hGc, ← hJ, hM, hM, hM, GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places, GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places]
  have h1 : ∀ τ i j, (Z τ i j * conj ((Complex.I • Y) τ i j)).im = -(Z τ i j * conj (Y τ i j)).re := by
    intro τ i j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [h1]
  have h2 : ∀ τ i j, (fw D τ : ℂ) * Z τ i j * conj (Y τ i j) =
      (2 * Real.pi * ‖tauE D τ D.host.xi0‖ : ℝ) * (((Z τ i j * conj (Y τ i j)).re : ℂ) +
        ((Z τ i j * conj (Y τ i j)).im : ℂ) * Complex.I) := by
    intro τ i j
    rw [Complex.re_add_im, fw, mul_assoc]
  simp only [h2]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, neg_neg]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

end GlobalTheory.FockEntire
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fockGaussianReading_differentiable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ x, Differentiable ℂ (rd ψ σ A B f x) := by
  first | exact @GlobalTheory.FockEntire.rd_differentiable | exact GlobalTheory.FockEntire.rd_differentiable | (intros; apply GlobalTheory.FockEntire.rd_differentiable <;> assumption)
end
end
