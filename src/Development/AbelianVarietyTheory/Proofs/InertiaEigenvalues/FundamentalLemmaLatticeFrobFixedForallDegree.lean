module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumnStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumnsStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  first | exact @GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | exact GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | (intros; apply GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fundamentalLemmaLattice_degreeOne : FLAt 1 := by
  first | exact @GlobalTheory.PMon.FLOne.flAt_one | exact GlobalTheory.PMon.FLOne.flAt_one | (intros; apply GlobalTheory.PMon.FLOne.flAt_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrix

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem fil_mul_entries {n : Type} [Fintype n] {A B : Matrix n n P.R.BdR}
    (hA : ∀ i j, A i j ∈ Fil P 0) (hB : ∀ i j, B i j ∈ Fil P 0) : ∀ i j, (A * B) i j ∈ Fil P 0 :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)

theorem fil_blockDiagonal_entries {r : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (V : Fin r → Matrix n n P.R.BdR) (h : ∀ m i j, V m i j ∈ Fil P 0) :
    ∀ a b, Matrix.blockDiagonal V a b ∈ Fil P 0 := fun a b => by
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact h _ _ _
  · exact Fil_zero_mem 0

theorem fil_kd_entries {m : Type} [Fintype m] [DecidableEq m] (g : GL m ↥(MaximalUnramifiedExtension l)) :
    ∀ a b, ((Units.map ((kd P).mapMatrix : Matrix m m ↥(MaximalUnramifiedExtension l) →+* Matrix m m P.R.BdR).toMonoidHom g :
      GL m P.R.BdR) : Matrix m m P.R.BdR) a b ∈ Fil P 0 := fun a b => by
  rw [Units.coe_map]
  exact kd_mem_Fil P _

theorem unitM_U0_of_unitM : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR),
    (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  intro l _ P r ω hdet n _ _ U hU
  constructor
  · unfold U0
    rw [Units.val_mul, ← map_inv]
    exact fil_mul_entries (fil_kd_entries _)
      (fil_blockDiagonal_entries _ fun m i j => (hU m).1 i j)
  · unfold U0
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    exact fil_mul_entries
      (fil_blockDiagonal_entries _ fun m i j => (hU m).2 i j) (fil_kd_entries _)

end GlobalTheory.PMon.ResR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrixStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR), (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  first | exact @GlobalTheory.PMon.ResR.unitM_U0_of_unitM | exact GlobalTheory.PMon.ResR.unitM_U0_of_unitM | (intros; apply GlobalTheory.PMon.ResR.unitM_U0_of_unitM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem colv_latC_and_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  intro l _ P r ω hω hdet n _ _ U x y A₀ hA W₀ hW hev
  have hit : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] b = (P.φB ^ m) b := fun m b => by rw [AlgHom.coe_pow]
  have hfix : ∀ (m : ℕ) i j, P.φB^[m] ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun m i j => Function.iterate_fixed (hA i j) m
  have hφcol : ∀ (m : ℕ) c i, P.φB^[m] (colv P ω A₀ c i) =
      ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c := by
    intro m c i

    rw [hit, colv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hit, ← hit, phi_iter_kur, hfix]
  have hsum : ∀ {R : Type} [CommRing R] (f : ↥(MaximalUnramifiedExtension l) →+* R) (X : Matrix (n × Fin r) (n × Fin r) R) (m : Fin r) (i : n) c,
      ∑ k, f (fr l m (ω k)) * X (i, k) c = ((resMat n ω).map f * X) (i, m) c := by
    intro R _ f X m i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [resMat_apply, apply_ite f, ite_mul]
  have hpU : (resMat n ω).map (kd P) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
      Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR) := by
    have e : (resMat n ω).map (kd P) = ((Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
        Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) : GL (n × Fin r) P.R.BdR) :
        Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
    rw [e, U0, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rfl
  have h0 : ∀ e f, P.ιB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) e f) =
      ((U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) e f := by
    intro e f; rw [← hev]; rfl
  have hcol : ∀ (m : Fin r) c i, ev P m (colv P ω A₀ c i) =
      ∑ j, (U m : Matrix n n P.R.BdR) i j * tz P (eps x y (m, j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c := by
    intro m c i

    rw [ev, hφcol, map_sum]
    simp only [map_mul, iota_kur, h0]
    rw [hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_mul, ite_mul, mul_assoc]
  refine ⟨fun c => ⟨fun i => ?_, fun m => ⟨fun j => (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c,
    fun j => hW.1 _ _, funext fun i => ?_⟩⟩, ?_⟩
  · rw [hφcol]; simp only [hω]; rfl
  · rw [hcol]; simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
  · haveI : Nontrivial P.R.BdR := ⟨⟨(P.PD (botExt l)).ι (P.PD (botExt l)).t, 0, fun h =>
      (P.PD (botExt l)).not_mem_filtration_two (by rw [h]; exact zero_mem _)⟩⟩
    haveI : Nontrivial P.R.B := ⟨⟨1, 0, fun h => one_ne_zero (by simpa using congrArg P.ιB h : (1 : P.R.BdR) = 0)⟩⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ c, g c • colv P ω A₀ c i = 0 := fun i => by
      have := congrFun hg i; simpa [Finset.sum_apply] using this
    have hYe : ∀ i (m : Fin r) c, Ymat P ω A₀ (i, m) c = P.φB^[m] (colv P ω A₀ c i) := by
      intro i m c
      rw [hφcol, hsum, Ymat]
    have hY : (Ymat P ω A₀).mulVec (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      funext ⟨i, m⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      calc ∑ c, Ymat P ω A₀ (i, m) c * algebraMap ℚ_[l] P.R.B (g c)
          = (P.φB ^ (m : ℕ)) (∑ c, g c • colv P ω A₀ c i) := by

            rw [map_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [hYe, hit, map_smul, Algebra.smul_def, mul_comm]
        _ = 0 := by rw [hg' i, map_zero]
    have hdetY : IsUnit (Ymat P ω A₀).det := by
      rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((isUnit_det_resMat n ω hdet).map _).mul ((Matrix.isUnit_iff_isUnit_det _).1 A₀.isUnit)
    have hv0 : (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      have := congrArg (Matrix.mulVec (Ymat P ω A₀)⁻¹) hY
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetY, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    intro c
    exact (algebraMap ℚ_[l] P.R.B).injective (by simpa using congrFun hv0 c)

end GlobalTheory.PMon.ResR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndependStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  first | exact @GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | exact GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | (intros; apply GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := GlobalTheory.T.fundamentalLemmaLattice_degreeOne l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix l P r ω hdet' n U hU) (GlobalTheory.T.linearIndependent_restrictionLattice_column l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => GlobalTheory.T.mem_span_restrictionLattice_columns l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed l P r n U x y _ e he (h3.1 c)))
  exact GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
end
end
