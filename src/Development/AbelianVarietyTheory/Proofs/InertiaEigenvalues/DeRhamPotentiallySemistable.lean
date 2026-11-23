module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRiStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.LocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixFormStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDRStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  first | exact @GlobalTheory.DRMat.exists_period_matrix_of_isDR | exact GlobalTheory.DRMat.exists_period_matrix_of_isDR | (intros; apply GlobalTheory.DRMat.exists_period_matrix_of_isDR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrictStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  first | exact @GlobalTheory.PMon.isPst_of_isSst_resTo | exact GlobalTheory.PMon.isPst_of_isSst_resTo | (intros; apply GlobalTheory.PMon.isPst_of_isSst_resTo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FromMat

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {n : Type} [Fintype n] [DecidableEq n]

def matRep (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) :=
  MonoidHom.toHomUnits
    ((((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).mapMatrix : Matrix n n ℚ_[l] →+* Matrix n n ↥(MaximalUnramifiedExtension l)) :
        Matrix n n ℚ_[l] →* Matrix n n ↥(MaximalUnramifiedExtension l)).comp
      (((LinearMap.toMatrixAlgEquiv b : (V →ₗ[ℚ_[l]] V) ≃ₐ[ℚ_[l]] Matrix n n ℚ_[l]) :
        (V →ₗ[ℚ_[l]] V) →* Matrix n n ℚ_[l]).comp ρ))

theorem matRep_apply (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (i j : n) :
    (matRep b ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (b.repr (ρ g (b j)) i) := by
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply]

theorem toMatrix_map_apply (b : Module.Basis n ℚ_[l] V) (f : V →ₗ[ℚ_[l]] V) {A : Type} [Semiring A] [Algebra ℚ_[l] A]
    (i j : n) : (LinearMap.toMatrix b b f).map (algebraMap ℚ_[l] A) i j = algebraMap ℚ_[l] A (b.repr (f (b j)) i) := by
  simp [LinearMap.toMatrix_apply]

end GlobalTheory.PMon.FromMat

namespace GlobalTheory.PMon.FromMat

open GlobalTheory.PMon.Inhab

theorem deRhamPotSemistable_of_matThm : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  intro hM l _ P AI hT K V _ _ _ _ _ ρ hc hDR
  obtain ⟨T⟩ := hT
  let b := Module.finBasis ℚ_[l] V
  have hR : IsRat 1 (matRep b ρ) := by
    refine ⟨one_pos, fun c hc' => ?_, fun g i j => ?_, fun i j => ?_⟩
    · obtain ⟨q, rfl⟩ := fixed_frob P c (by rwa [fr_one] at hc')
      exact K.1.algebraMap_mem q
    · rw [matRep_apply, fr_q]
    · simp only [matRep_apply]
      have h1 : Continuous fun g : ↥(GK K) => b.coord i (ρ g (b j)) :=
        (IsModuleTopology.continuous_of_linearMap (R := ℚ_[l]) (b.coord i)).comp (hc (b j))
      exact (continuous_algebraMap ℚ_[l] (Om l)).comp h1
  have hD : AdmDR P (matRep b ρ) := by
    intro m
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR l P AI T _ K V b ρ hDR
    refine ⟨Q, fun g => ?_⟩
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    rw [matD, Matrix.map_apply, matRep_apply, fr_q, kd_alg, toMatrix_map_apply]
  obtain ⟨K', hK, Q, hQ⟩ := hM l P AI T _ K 1 (matRep b ρ) hR hD
  have hS : IsSst P (resTo ρ hK) := by
    refine GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T _ K' V b (resTo ρ hK) Q fun g => ?_
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [matRep_apply, LinearMap.toMatrix_apply, ks, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      Polynomial.algebraMap_apply]
    rfl
  exact GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict l P AI T K K' hK V ρ hS

end GlobalTheory.PMon.FromMat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  first | exact @GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | exact GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | (intros; apply GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory

theorem deRham_potentiallySemistable : GlobalTheory.Published.DeRhamPotSemistable :=
  GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy GlobalTheory.T.pAdicMonodromyTheorem_matrixForm

end GlobalTheory
end
end
