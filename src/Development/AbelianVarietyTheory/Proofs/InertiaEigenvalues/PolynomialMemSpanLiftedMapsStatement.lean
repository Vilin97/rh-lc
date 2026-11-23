module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
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
public import ReciprocityTheory.DualLattices.ConstantCoeffRowSubst
import ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurIsotypicSplittingInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariant

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links MvPolynomial Matrix
open scoped Classical

namespace GlobalTheory.FockIsotypic

variable {D : D7} {m n : ℕ}

def fvarRegroup (D : D7) (m n : ℕ) : FVar D m n ≃ Fin n × (D.what₂.Tau × Fin m) where
  toFun v := (v.2.2, (v.1, v.2.1))
  invFun w := (w.2.1, w.2.2, w.1)
  left_inv _ := rfl
  right_inv _ := rfl

def flatRegroup (D : D7) (m n : ℕ) : Fin (Fintype.card (FVar D m n)) ≃ Fin n × (D.what₂.Tau × Fin m) :=
  (Equiv.prodPUnit _).symm.trans ((flat (FVar D m n)).symm.trans (fvarRegroup D m n))

def fockBlock (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (k : D.what₂.Tau × Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if k.2.val < p k.1 then ((((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ else ((U k.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

def fockMat (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) :
    Matrix (Fin (Fintype.card (FVar D m n))) (Fin (Fintype.card (FVar D m n))) ℂ :=
  (blockDiagonal (fockBlock (m := m) p U)).submatrix (flatRegroup D m n) (flatRegroup D m n)

theorem rename_fockSubst (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (P : PolF D m n) :
    rename (flat (FVar D m n)) (GlobalTheory.ExportSeries.fockSubst p U P) =
      ReciprocityTheory.PGsh.rowSubst (fockMat p U) (rename (flat (FVar D m n)) P) := by
  have key : (rename (flat (FVar D m n))).comp (GlobalTheory.ExportSeries.fockSubst p U) =
      (ReciprocityTheory.PGsh.rowSubst (fockMat p U)).comp (rename (flat (FVar D m n))) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (flatRegroup D m n).symm.sum_comp, Fintype.sum_prod_type_right,
      Finset.sum_eq_single (v.1, v.2.1)]
    · have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      have hx : ∀ b : Fin n, ((flatRegroup D m n).symm (b, (v.1, v.2.1)), (flat (FVar D m n) v).2) =
          flat (FVar D m n) (v.1, v.2.1, b) := fun b => by
        simp [flatRegroup, fvarRegroup]
      simp only [fockMat, submatrix_apply, Equiv.apply_symm_apply, hv, blockDiagonal_apply_eq, hx]
      split_ifs with h <;> simp [fockBlock, h, map_sum, rename_X]
    · intro k _ hk
      refine Finset.sum_eq_zero fun b _ => ?_
      have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      simp [fockMat, hv, blockDiagonal_apply_ne _ _ _ hk]
    · simp
  exact congrArg (fun f => f P) key

theorem fockBlock_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (k : D.what₂.Tau × Fin m) :
    (fockBlock p U k)ᴴ * fockBlock p U k = 1 := by
  have hu := hU k.1
  rw [Matrix.mem_unitaryGroup_iff] at hu
  have hu' := hU k.1
  rw [Matrix.mem_unitaryGroup_iff'] at hu'
  unfold fockBlock
  split_ifs
  · have hinv : (((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star (U k.1).val :=
      Units.inv_eq_of_mul_eq_one_right hu
    rw [hinv]
    ext i j
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun hu' i) j)

    simp only [Matrix.mul_apply, Matrix.star_apply, map_sum, map_mul, Complex.conj_conj, RCLike.star_def] at this
    have h1 : ((star (U k.1).val)ᵀᴴ * (star (U k.1).val)ᵀ) i j =
        ∑ x, (U k.1).val x i * starRingEnd ℂ ((U k.1).val x j) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def,
        Complex.conj_conj]
    rw [h1, this, Matrix.one_apply]
    split_ifs <;> simp
  · simpa [Matrix.star_eq_conjTranspose] using hu'

theorem fockMat_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (fockMat (m := m) p U)ᴴ * fockMat p U = 1 := by
  rw [fockMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp only [fockBlock_conjTranspose_mul p U hU]
  rw [show (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : D.what₂.Tau × Fin m → Matrix (Fin n) (Fin n) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fis_fockSubst_of_unitary (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (P Q : PolF D m n) :
    fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = fis P Q := by
  unfold fis
  rw [rename_fockSubst, rename_fockSubst, ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul,
    fockMat_conjTranspose_mul p U hU, ReciprocityTheory.PGsh.rowSubst_one]

end GlobalTheory.FockIsotypic
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links

theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  first | exact @GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | exact GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | (intros; apply GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitution

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.RealFockActionFree

open GlobalTheory.ExportSeries
open scoped ComplexOrder

theorem om_ptP_inf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t u hu
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨fun τ => ((Wc D i).sig (tauE D τ)).1, c, U, hU, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := fun τ => ((Wc D i).sig (tauE D τ)).1) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf, LinearMap.map_smul]

end GlobalTheory.RealFockActionFree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitutionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  first | exact @GlobalTheory.RealFockActionFree.om_ptP_inf | exact GlobalTheory.RealFockActionFree.om_ptP_inf | (intros; apply GlobalTheory.RealFockActionFree.om_ptP_inf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMaps

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockIsotypic

theorem isotypic_split : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := GlobalTheory.T.schur_isotypic_splitting_inner_product

theorem fis_fockSubst : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant

theorem om_ptP_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution

theorem totalDegree_aeval_le {σ κ : Type} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (AddMonoidAlgebra.coeff P s)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_fockSubst_le {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (P : PolF D m n) : (GlobalTheory.ExportSeries.fockSubst p U P).totalDegree ≤ P.totalDegree := by
  unfold GlobalTheory.ExportSeries.fockSubst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs
  all_goals
    refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem decomp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hgiv _ i t P
  have hC := hgiv.core
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t).2.2
  have hcV : (R.cV i).Is := hC.models.cV i
  haveI : Nontrivial (R.cV i).W := hcV.2.2.2.1
  choose p c U hU hω using fun g : GinfC (Vc D i) => om_ptP_fock D G Pl0 T A Ks R F hC i t g.1 g.2
  let actL : GinfC (Vc D i) → Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    fun g => c g • (GlobalTheory.ExportSeries.fockSubst (p g) (U g)).toLinearMap
  have hact : ∀ g Q, R.ptP i t (actL g Q) = R.ωP i t (g.1, 1) (R.ptP i t Q) := fun g Q => (hω g Q).symm
  have hmul : ∀ g h Q, actL (g * h) Q = actL g (actL h Q) := fun g h Q => hinj (by
    have e : (((g * h : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = ((g : GA D (Vc D i)), 1) * ((h : GA D (Vc D i)), 1) := by
      simp
    rw [hact, hact, hact, e, map_mul, Module.End.mul_apply])
  have hone : ∀ Q, actL 1 Q = Q := fun Q => hinj (by
    have e : (((1 : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 := by simp
    rw [hact, e, map_one, Module.End.one_apply])
  let S : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    MvPolynomial.restrictTotalDegree (FVar D (Wc D i).rank (Vc D i).rank) ℂ P.totalDegree
  have hS : ∀ g, ∀ Q ∈ S, actL g Q ∈ S := fun g Q hQ => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
    exact (MvPolynomial.totalDegree_smul_le _ _).trans ((totalDegree_fockSubst_le _ _ _).trans hQ)
  letI : InnerProductSpace.Core ℂ S := fisCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  let actS : GinfC (Vc D i) →* Module.End ℂ S :=
    { toFun := fun g => (actL g).restrict (hS g)
      map_one' := LinearMap.ext fun x => Subtype.ext (hone x.1)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (hmul g h x.1) }
  have hconf : ∀ g (x y : S), inner ℂ x y = 0 → inner ℂ (actS g x) (actS g y) = 0 := by
    intro g x y h
    change fis (actL g y.1) (actL g x.1) = 0
    change fis y.1 x.1 = 0 at h
    simp only [actL, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [fis_smul_left, fis_smul_right, fis_fockSubst _ _ _ _ _ (hU g), h, mul_zero, mul_zero]
  let ρ' : GinfC (Vc D i) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype
  have hirr : ∀ W' : Submodule ℂ (R.cV i).W, (∀ g, W'.map (ρ' g) ≤ W') → W' = ⊥ ∨ W' = ⊤ :=
    fun W' hW => hcV.2.2.2.2 W' fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hW ⟨a, ha⟩
  obtain ⟨q, hq, E, hEst, hEs, hxE⟩ :=
    isotypic_split actS hconf ρ' hirr ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  refine ⟨q.1, ?_, E.map S.subtype, inferInstance, ?_, ?_, ⟨_, hxE, rfl⟩⟩
  · refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span S.subtype hq)
    rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
    refine ⟨S.subtype ∘ₗ φ, w, fun u hu w' => ?_, rfl⟩
    have e := congrArg Subtype.val (hφ ⟨u, hu⟩ w')
    show R.ptP i t (φ (ρ' ⟨u, hu⟩ w')).1 = R.ωP i t (u, 1) (R.ptP i t (φ w').1)
    rw [e]
    exact hact ⟨u, hu⟩ _
  · rintro u hu _ ⟨e, he, rfl⟩ P₂ h
    have e2 : P₂ = actL ⟨u, hu⟩ e.1 := hinj (h.trans (hact ⟨u, hu⟩ e.1).symm)
    exact ⟨actS ⟨u, hu⟩ e, hEst _ e he, e2.symm⟩
  · intro φ' hφ'
    let ev := Module.evalEquiv ℂ (R.cV i).W
    let φ : S →ₗ[ℂ] (R.cV i).W := ev.symm.toLinearMap ∘ₗ φ' ∘ₗ S.subtype
    have hφe : ∀ x : S, ev (φ x) = φ' x.1 := fun x => ev.apply_symm_apply _
    have key : ∀ g, ∀ e ∈ E, φ (actS g e) = ρ' g (φ e) := by
      intro g e he
      apply ev.injective
      rw [hφe]
      ext l
      have h1 := hφ' g.1 g.2 e.1 ⟨e, he, rfl⟩ (actL g e.1) (hact g e.1) l
      change φ' (actL g e.1) l = _
      rw [h1, ← hφe e]
      rfl
    rintro _ ⟨e, he, rfl⟩
    rw [Submodule.subtype_apply, ← hφe e, hEs φ key e he, map_zero]

end GlobalTheory.FockIsotypic

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMapsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.polynomial_mem_span_lifted_maps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  first | exact @GlobalTheory.FockIsotypic.decomp | exact GlobalTheory.FockIsotypic.decomp | (intros; apply GlobalTheory.FockIsotypic.decomp <;> assumption)
end
end
