module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryRestrictionScalarsBlockZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalarsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobeniusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalarsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatementStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonalStatement
import GroundTheory.LocalFields.Examples
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumns

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonCob

theorem coboundary_cols (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P) :
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  intro h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] (ι → Bst P) :=
    TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : ι → ℚ_[l]) (a : Bst P) (x : ι) => v x • a)
      (fun v w a => by funext x; simp [add_smul])
      (fun c v a => by funext x; simp [mul_smul])
      (fun v a a' => by funext x; simp [smul_add])
      (fun c v a => by funext x; simp [smul_comm c]))
  have hΦ : ∀ (v : ι → ℚ_[l]) (a : Bst P), Φ (v ⊗ₜ a) = fun x => v x • a := fun v a => by
    simp [Φ]
  have hst : ∀ (g : ↥(GK K)) (y : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
      Φ (stRep P (repOf ρ₀) g y) = ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (Φ y x)) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => funext x; simp [Matrix.mulVec, dotProduct]
    | tmul v a =>
      rw [stRep_tmul, repOf_apply, hΦ, hΦ]
      funext x
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
    | add y z hy hz =>
      rw [map_add (f := _), map_add (f := _), hy, hz, ← Matrix.mulVec_add]
      congr 1
      funext x
      simp
  refine ⟨Φ b, fun g => ?_⟩
  have := congrArg Φ (h g)
  rw [map_sub, hst, hΦ] at this
  rw [← this]
  funext x
  simp [Algebra.algebraMap_eq_smul_one]

end GlobalTheory.PMonCob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumnsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.coboundary_semistableTensor_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMonCob.coboundary_cols | exact GlobalTheory.PMonCob.coboundary_cols | (intros; apply GlobalTheory.PMonCob.coboundary_cols <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRham

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CobColumn

theorem coboundary_tmul_of_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  intro l _ P K ι _ _ ρ₀ c₀ β h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (ι → P.R.BdR) :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).toLinearMap ∘ₗ (TensorProduct.comm ℚ_[l] _ _).toLinearMap
  have hΦinj : Function.Injective Φ :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).injective.comp (TensorProduct.comm ℚ_[l] _ _).injective
  have hΦ : ∀ v b i, Φ (v ⊗ₜ b) i = algebraMap ℚ_[l] P.R.BdR (v i) * b := by
    intro v b i
    simp [Φ, piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]
  have hact : ∀ g v b, actVdR (P.PD K) (repOf ρ₀) g (v ⊗ₜ b) = repOf ρ₀ g v ⊗ₜ P.actQdR (g : GQ l) b := by
    intro g v b
    rw [← P.PD_actdR K g b]
    rfl
  refine ⟨∑ x, Pi.single x 1 ⊗ₜ β x, fun g => hΦinj ?_⟩
  funext i
  have hi := congrFun (h g) i

  simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hact, hΦ, repOf_apply, mul_one]
  rw [hi]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne' hx]
    · simp

end GlobalTheory.CobColumn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRhamStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.coboundary_tmul_of_column_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  first | exact @GlobalTheory.CobColumn.coboundary_tmul_of_column | exact GlobalTheory.CobColumn.coboundary_tmul_of_column | (intros; apply GlobalTheory.CobColumn.coboundary_tmul_of_column <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoords

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.cocycle_rat_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  intro l _ n _ _ K r σ ρ₀ p c c₀ hint hc0 hc g h
  set f : ℚ_[l] →+* ↥(MaximalUnramifiedExtension l) := algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) with hf
  set P : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hP

  have hC : (fun x : n × Fin r => fr l x.2 (c (g * h) x.1)) =
      (fun x : n × Fin r => fr l x.2 (c g x.1)) +
        (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).mulVec
          (fun x : n × Fin r => fr l x.2 (c h x.1)) := by
    funext ⟨i, m⟩

    simp only [hc, Pi.add_apply, map_add (f := _), Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, Matrix.map_apply, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have key : P.mulVec (fun x => f (c₀ (g * h) x)) =
      P.mulVec (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    rw [hc0, hC, ← hc0 g, ← hc0 h, Matrix.mulVec_mulVec, ← hint g]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    congr 1
    congr 1
    funext x
    simp only [Pi.add_apply, map_add, RingHom.map_mulVec, Function.comp_def]
  have inj : (fun x => f (c₀ (g * h) x)) =
      (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    have := congrArg (fun v => ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec v) key
    simp only [hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this
  funext x
  exact f.injective (congrFun inj x)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoordsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.cocycle_restrictionScalars_rational_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  first | exact @GlobalTheory.PMon.cocycle_rat_coords | exact GlobalTheory.PMon.cocycle_rat_coords | (intros; apply GlobalTheory.PMon.cocycle_rat_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo_mat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P AI T n _ _ K r σ Q hσ hQ c hcr hcc hcoc hdR
  obtain ⟨ω, W, hW, hω, hcoef⟩ := GlobalTheory.T.exists_continuous_coords_unramified_frobenius l r hσ.pos
  obtain ⟨ρ₀, p, hρc, hpK, hint, hc₀⟩ := GlobalTheory.T.exists_rational_form_unramified_restrictionScalars l n K r σ ω W hσ hW hω hcoef
  obtain ⟨c₀, hc₀c, hpc⟩ := hc₀ c hcr hcc
  have hcoc₀ := GlobalTheory.T.cocycle_restrictionScalars_rational_coords l n K r σ ρ₀ p c c₀ hint hpc hcoc
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.T.periodMatrix_restrictionScalars_blockDiagonal l P n K r σ Q ρ₀ p hQ hpK hint
  have hsst : IsSst P (repOf ρ₀) :=
    GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T (n × Fin r) K (n × Fin r → ℚ_[l]) (Pi.basisFun ℚ_[l] _) (repOf ρ₀) Q₀
      (fun g => by rw [toMatrix_repOf]; exact hQ₀ g)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.deRham_trivial_rational_cocycle_restrictionScalars l P n K r σ ρ₀ p c c₀ hpK hint hpc hdR
  obtain ⟨bd, hbd⟩ := GlobalTheory.T.coboundary_tmul_of_column_deRham l P K _ ρ₀ c₀ β hβ
  have hcontρ : ∀ v : n × Fin r → ℚ_[l], Continuous fun g => repOf ρ₀ g v := by
    intro v
    simp only [repOf_apply]
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hρc i j).mul continuous_const
  obtain ⟨bs, hbs⟩ := GlobalTheory.T.hyodo_statement l P AI T K (n × Fin r → ℚ_[l]) (repOf ρ₀) hcontρ hsst c₀ hc₀c
    hcoc₀ ⟨bd, hbd⟩
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.coboundary_semistableTensor_columns l P K _ ρ₀ c₀ bs hbs
  exact GlobalTheory.T.coboundary_restrictionScalars_block_zero l P n K r hσ.pos σ ρ₀ p c c₀ β' hpK hint hpc hβ'

end GlobalTheory.PMon

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficientsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  first | exact @GlobalTheory.PMon.hyodo_mat | exact GlobalTheory.PMon.hyodo_mat | (intros; apply GlobalTheory.PMon.hyodo_mat <;> assumption)
end
end
