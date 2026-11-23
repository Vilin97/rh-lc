module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRhamStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuouStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistable

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem kroneckerMap_mul_map_ringHom {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (f : R →+* S)
    (A : Matrix a a R) (B : Matrix b b R) :
    (Matrix.kroneckerMap (· * ·) A B).map f = Matrix.kroneckerMap (· * ·) (A.map f) (B.map f) := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

theorem inv_periodMatrix_map_mul_eq_inv {S T : Type*} [CommRing S] [CommRing T] {b : Type*} [Fintype b] [DecidableEq b]
    (k : S →+* T) (σ : T →+* T) (r : GL b S) (Q : GL b T)
    (h : (r : Matrix b b S).map k * (Q : Matrix b b T).map σ = Q) :
    ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k = ((Q⁻¹ : GL b T) : Matrix b b T) := by
  have hQ : (Q : Matrix b b T) * (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) = 1 := by
    rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc ((Q : Matrix b b T).map σ), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero k) (map_one k)]
  calc ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k
      = ((Q⁻¹ : GL b T) : Matrix b b T) * (Q : Matrix b b T) *
          (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) := by
        rw [Units.inv_mul, Matrix.one_mul]
    _ = ((Q⁻¹ : GL b T) : Matrix b b T) := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem homUnit_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  intro l _ P a b _ _ _ _ K ρ₁ ρ₂ Q₁ Q₂ h₁ h₂ g
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have e : ∀ {n : Type} (M : Matrix n n (Bst P)), M.map (actSt P (g : GQ l)) = M.map σ := fun M => rfl
  have h1 := h₁ g
  have h2 := h₂ g
  rw [e] at h1 h2
  rw [e, homRep_apply, homUnit_val, homUnit_val, kroneckerMap_mul_map_ringHom, kroneckerMap_mul_map_ringHom, ← Matrix.mul_kronecker_mul, h1,
    Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul, inv_periodMatrix_map_mul_eq_inv (ks P) σ (ρ₂ g) Q₂ h2]

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.matrixHom_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  first | exact @GlobalTheory.PMon.homUnit_period | exact GlobalTheory.PMon.homUnit_period | (intros; apply GlobalTheory.PMon.homUnit_period <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem extStep_holds : ExtStep := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c hρ hblk hdR h₁ h₂
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  obtain ⟨K₂, hK₂, Q₂, hQ₂⟩ := h₂
  haveI := K₁.2
  haveI := K₂.2
  let K' : FinExt l := ⟨K₁.1 ⊔ K₂.1, inferInstance⟩
  have h1' : K₁.1 ≤ K'.1 := le_sup_left
  have h2' : K₂.1 ≤ K'.1 := le_sup_right
  have hK : K.1 ≤ K'.1 := hK₁.trans h1'
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  have hQ₁' : ∀ g : ↥(GK K'), ((ρ₁.comp ι) g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁ := fun g => hQ₁ ⟨g, GK_le h1' g.2⟩
  have hQ₂' : ∀ g : ↥(GK K'), ((ρ₂.comp ι) g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂ := fun g => hQ₂ ⟨g, GK_le h2' g.2⟩
  have hdR₂ : AdmDR P ρ₂ := (GlobalTheory.T.deRham_blockTriangular_diagonal_blocks l P AI T a b K r ρ ρ₁ ρ₂ c hρ hblk hdR).2
  obtain ⟨hcr, hcc, hcoc⟩ := GlobalTheory.T.matrixHomRepresentationCocycle_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk
  obtain ⟨v, hv⟩ := GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients l P AI T (a × b) K' r (homRep (ρ₁.comp ι) (ρ₂.comp ι)) (homUnit Q₁ Q₂)
    (GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk) (GlobalTheory.T.matrixHom_periodMatrix_semistable l P a b K' (ρ₁.comp ι) (ρ₂.comp ι) Q₁ Q₂ hQ₁' hQ₂')
    (extCoc (ρ₂.comp ι) (fun g => c (ι g))) hcr hcc hcoc
    (fun m => by
      obtain ⟨w, hw⟩ := GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham l P AI T a b K ρ ρ₁ ρ₂ c hblk hdR hdR₂ m
      exact ⟨w, fun g => hw (ι g)⟩)
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.extension_block_periodMatrix_semistable l P a b K' (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hblk (ι g))
    Q₁ Q₂ hQ₁' hQ₂' v hv
  exact ⟨K', hK, Q, fun g => hQ g⟩

end GlobalTheory.PMon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRhamExtension_potentiallySemistable : ExtStep := by
  first | exact @GlobalTheory.PMon.extStep_holds | exact GlobalTheory.PMon.extStep_holds | (intros; apply GlobalTheory.PMon.extStep_holds <;> assumption)
end
end
