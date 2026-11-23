module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorReadingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorMultiplierAntilinear

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem map_inv_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.adjugate.map f = (M.map f).adjugate := by
    have := RingHom.map_adjugate f M; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (M.map f).det = f M.det := by
    have := RingHom.map_det f M; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem formAt_eq_omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.OrientedHeis.formAt S T τ x y = GlobalTheory.VacUnique.omAt S T τ x y := by
  unfold GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt
  congr 3
  rw [gramAt, gramAt, ← map_inv_ringHom]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem omF_eq {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B z e = GlobalTheory.VacUnique.omO S T (fmR A B z) (fmR A B e) := by
  rw [GlobalTheory.VacUnique.omO_apply]
  exact Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _

theorem cplxO_smulC' {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum' {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem fmR_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (I • z) = GlobalTheory.VacUnique.jO S T A.cart B.cart (fmR A B z) := by
  funext τ
  show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))
  have hs := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1
  have ht := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1
  unfold fockMat
  rw [cplxO_sum']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]
  have e1 : ((I • z) τ i j).re = -(z τ i j).im := by simp
  have e2 : ((I • z) τ i j).im = (z τ i j).re := by simp
  rw [e1, e2]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]
  abel

theorem fmR_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (z + w) = fmR A B z + fmR A B w := by
  funext τ
  show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
  simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel

theorem fmR_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (c • z) = c • fmR A B z := by
  funext τ
  show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
  simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_smul]

theorem omF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (z + w) e = omF A B z e + omF A B w e := by
  rw [omF_eq, omF_eq, omF_eq, fmR_add, map_add (f := _), LinearMap.add_apply]

theorem omF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (c • z) e = c * omF A B z e := by
  rw [omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem omF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) e = -omF A B z (I • e) := by
  obtain ⟨hJJ, -, hinv, -⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
  rw [omF_eq, omF_eq, fmR_I, fmR_I]
  set J := GlobalTheory.VacUnique.jO S T A.cart B.cart
  set x := fmR A B z
  set y := fmR A B e
  have hy : y = -J (J y) := by rw [hJJ, neg_neg]
  conv_lhs => rw [hy]
  rw [map_neg, hinv]

theorem omF_I_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) (I • e) = omF A B z e := by
  rw [omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]
  have : fmR A B (-e) = -fmR A B e := by
    have h := fmR_smul A B (-1) e
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [this, map_neg, neg_neg]

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem gD_add (c : ι → ℝ) (z w e : VCx ι a b) : gD c (z + w) e = gD c z e + gD c w e := by
  simp only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem gD_smul (c : ι → ℝ) (r : ℝ) (z e : VCx ι a b) : gD c (r • z) e = r * gD c z e := by
  simp only [gD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  ring

theorem gD_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) e = -gD c z (I • e) := by
  simp only [gD, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

theorem gD_I_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) (I • e) = gD c z e := by
  simp only [gD]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

end GlobalTheory.FockTransl.Jet

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem lamF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z w : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (z + w) = lamF A B l z + lamF A B l w := by
  simp only [lamF, omF_add, gD_add]
  push_cast
  ring

theorem lamF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (r : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (r • z) = r * lamF A B l z := by
  simp only [lamF, omF_smul, gD_smul]
  push_cast
  ring

theorem lamF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (I • z) = -I * lamF A B l z := by
  simp only [lamF]
  rw [omF_I_I, omF_I, gD_I_I, gD_I]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) +
    (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq

theorem lamF_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  intro D S T A B l
  refine ⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩
  have e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a) := by
    funext τ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im t]
    ring
  have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp
  rw [e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]
  ring

end GlobalTheory.FockTransl.Jet

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorMultiplierAntilinearStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fockCreationOperatorMultiplier_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  first | exact @GlobalTheory.FockTransl.Jet.lamF_antilinear | exact GlobalTheory.FockTransl.Jet.lamF_antilinear | (intros; apply GlobalTheory.FockTransl.Jet.lamF_antilinear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem list_prod_toMultiset {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ) :
    ((Finsupp.toMultiset m).toList.map g).prod = m.prod fun l n => g l ^ n := by
  rw [Multiset.prod_map_toList]
  induction m using Finsupp.induction with
  | zero => simp
  | single_add a n g' ha hn ih =>
    rw [map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih, Finsupp.toMultiset_single, Finsupp.prod_add_index']
    · simp [Multiset.map_nsmul, Multiset.prod_nsmul]
    · simp
    · intro a b c; rw [pow_add]

theorem crOp_const_mul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (c : ℂ) (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) (hΦ : DifferentiableAt ℝ Φ z) :
    crOp A B l (fun z => c * Φ z) z = c * crOp A B l Φ z := by
  unfold crOp
  rw [fderiv_const_mul hΦ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem jet_eq_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  intro D ψ θ σ hψ hσ S T A B
  have L1 : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := GlobalTheory.T.fockCreationOperatorMultiplier_antilinear
  have L2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := GlobalTheory.T.fock_creation_operator_reading
  refine ⟨fun m => m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n, fun f hf x m => ?_⟩
  set Aop := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hent : Differentiable ℂ (rd ψ σ A B f x) := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf x
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ Formalism.L2.Ker.coordX (GlobalTheory.FockTransl.Jet.lamF A B) (rd ψ σ A B f x)
    (fun l => L1 D S T A B l) hent (GlobalTheory.FockTransl.Jet.crOp A B) (fun _ _ _ => rfl)
  have key : ∀ L : List (FVar D T.rank S.rank), rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x =
      fun z => (L.map fun l => 2 / (fockScale D l.1 : ℂ)).prod * L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x) z := by
    intro L
    induction L with
    | nil => funext z; simp
    | cons l L ih =>
      funext z
      have hd0 : Differentiable ℝ (L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x)) :=
        (hops L).1.differentiable (by simp)
      have hd : DifferentiableAt ℝ (rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x) z := by
        rw [ih]; exact ((hd0.const_mul _) z)
      rw [List.foldr_cons, L2 D ψ θ σ hψ hσ S T A B _ x l z hd, ih, GlobalTheory.FockTransl.Jet.crOp_const_mul A B l _ _ z (hd0 z),
        List.foldr_cons, List.map_cons, List.prod_cons]
      ring
  have h0 : ∀ h : WO S T → ℂ, rd ψ σ A B h x 0 = h x := by
    intro h
    have hz : fockPt σ A B (0 : VCx D.what₂.Tau S.rank T.rank) = 0 := by
      have e : (fun τ => fockMat A B τ ((0 : VCx D.what₂.Tau S.rank T.rank) τ)) = 0 := by
        funext τ; simp [fockMat]
      rw [fockPt, e]; exact (FockCompare.iotaW σ T S).map_zero
    simp [rd, gq, hz, GlobalTheory.OrientedHeis.heisO_zero]
  have hfs : ∀ l : FVar D T.rank S.rank, (fockScale D l.1 : ℂ) ≠ 0 := fun l => GlobalTheory.VacuumFockLaws.fockScale_ne l.1
  have hval : opPow Aop m f x = (m.prod fun l n => (2 / (fockScale D l.1 : ℂ)) ^ n) * derivAt0 (rd ψ σ A B f x) m := by
    rw [opPow, ← h0 (List.foldr _ f _), key]
    beta_reduce
    rw [(hops _).2, derivAt0, GlobalTheory.AdForm.JetRead.iter_cast _ _ _ (Multiset.length_toList _) Formalism.L2.Ker.coordX,
      list_prod_toMultiset]
  have hpt : GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x = opPow Aop m f x := by
    have e : MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ m = MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [GlobalTheory.ChainFr.ptF, pureTensorO, pureTensorL, ← e, Module.Basis.constr_basis]
  rw [hpt, hval, ← mul_assoc, ← Finsupp.prod_mul]
  have e1 : (m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n * (2 / (fockScale D l.1 : ℂ)) ^ n) = 1 := by
    refine Finset.prod_eq_one fun l _ => ?_
    beta_reduce
    rw [← mul_pow, div_mul_div_comm, mul_comm (fockScale D l.1 : ℂ) 2, div_self (mul_ne_zero two_ne_zero (hfs l)), one_pow]
  rw [e1, one_mul]

end GlobalTheory.FockTransl.Jet

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  first | exact @GlobalTheory.FockTransl.Jet.jet_eq_fock | exact GlobalTheory.FockTransl.Jet.jet_eq_fock | (intros; apply GlobalTheory.FockTransl.Jet.jet_eq_fock <;> assumption)
end
end
