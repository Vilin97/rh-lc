module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevel
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShiftStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevelStatement

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.card_range_mul_quotient_bounded_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | exact GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvariance

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegCov

section Ring

variable {A : Type} [CommRing A]

theorem cT_mul (τ : A →+* A) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) A)
    (y : Matrix (Fin b) (Fin c) A) : cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (τ : A →+* A) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem cT_cT (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) A) :
    cT τ (cT τ x) = x := by
  unfold cT
  ext i j
  exact hτ (x i j)

def covEquiv (τ : A →+* A) {m n : ℕ} (G G' : Matrix (Fin n) (Fin n) A)
    (P P' : Matrix (Fin m) (Fin m) A) (hG : G * G' = 1) (hG' : G' * G = 1)
    (hP : P * P' = 1) (hP' : P' * P = 1) :
    Matrix (Fin m) (Fin n) A ≃ Matrix (Fin m) (Fin n) A where
  toFun x := P' * x * cT τ G'
  invFun y := P * y * cT τ G
  left_inv x := by
    have h : cT τ G' * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    calc P * (P' * x * cT τ G') * cT τ G = (P * P') * x * (cT τ G' * cT τ G) := by
          simp only [Matrix.mul_assoc]
      _ = x := by rw [hP, h, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    have h : cT τ G * cT τ G' = 1 := by rw [← cT_mul, hG', cT_one]
    calc P' * (P * y * cT τ G) * cT τ G' = (P' * P) * y * (cT τ G * cT τ G') := by
          simp only [Matrix.mul_assoc]
      _ = y := by rw [hP', h, Matrix.one_mul, Matrix.mul_one]

theorem eq_of_conj (τ : A →+* A) {n : ℕ} {h D g g' : Matrix (Fin n) (Fin n) A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by
  have hg2 : cT τ g' * cT τ g = 1 := by rw [← cT_mul, hg, cT_one]
  rw [← hD]
  calc h = (cT τ g' * cT τ g) * h * (g * g') := by
        rw [hg2, hg, Matrix.one_mul, Matrix.mul_one]
    _ = cT τ g' * (cT τ g * h * g) * g' := by simp only [Matrix.mul_assoc]

theorem trace_cov (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {m n : ℕ}
    (D g' : Matrix (Fin n) (Fin n) A) (E p' : Matrix (Fin m) (Fin m) A)
    (x : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((cT τ g' * D * g') * (cT τ x * (cT τ p' * E * p') * x)) =
      Matrix.trace (D * (cT τ (p' * x * cT τ g') * E * (p' * x * cT τ g'))) := by
  rw [cT_mul, cT_mul, cT_cT τ hτ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (cT τ g')]
  simp only [Matrix.mul_assoc]

end Ring

section Red

variable {R : Type} [CommRing R]

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R)
    (y : Matrix (Fin b) (Fin c) R) : red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_cT (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ hf k (x j i)).symm

theorem red_one (ϖ : R) (k : ℕ) {a : ℕ} : red ϖ k (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  unfold red
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem barσ_inv (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [barσ_mk, barσ_mk, hσ]

end Red

theorem gauss_cov (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ)
    (hσ : ∀ a, σ (σ a) = a) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ)
    (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R)
    (hg : g * g' = 1) (hg' : g' * g = 1) (hp : p * p' = 1) (hp' : p' * p = 1)
    (hD : cT σ g * h * g = D) (hE : cT σ p * S * p = E) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) =
      ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  have hh : h = cT σ g' * D * g' := eq_of_conj σ hg hD
  have hS : S = cT σ p' * E * p' := eq_of_conj σ hp hE
  have rg : red ϖ k g * red ϖ k g' = 1 := by rw [← red_mul, hg, red_one]
  have rg' : red ϖ k g' * red ϖ k g = 1 := by rw [← red_mul, hg', red_one]
  have rp : red ϖ k p * red ϖ k p' = 1 := by rw [← red_mul, hp, red_one]
  have rp' : red ϖ k p' * red ϖ k p = 1 := by rw [← red_mul, hp', red_one]
  refine Fintype.sum_equiv
    (covEquiv (barσ σ ϖ hf k) (red ϖ k g) (red ϖ k g') (red ϖ k p) (red ϖ k p') rg rg' rp rp')
    _ _ ?_
  intro x
  have key : Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)) =
      Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')) *
        red ϖ k E * (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')))) := by
    rw [hh, hS, red_mul, red_mul, red_mul, red_mul, red_cT σ ϖ hf, red_cT σ ϖ hf]
    exact trace_cov (barσ σ ϖ hf k) (barσ_inv σ ϖ hf hσ k) (red ϖ k D) (red ϖ k g') (red ϖ k E)
      (red ϖ k p') x
  exact congrArg (⇑χ) key

end GlobalTheory.CompanionTheory.SiegCov
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvarianceStatement

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.matrix_gauss_sum_congr_invariance : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ), (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R), g * g' = 1 → g' * g = 1 → p * p' = 1 → p' * p = 1 → cT σ g * h * g = D → cT σ p * S * p = E → (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) = ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegCov.gauss_cov | exact GlobalTheory.CompanionTheory.SiegCov.gauss_cov | (intros; apply GlobalTheory.CompanionTheory.SiegCov.gauss_cov <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactor

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.GaussProd

theorem sum_pi_prod {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q] (g : ι → Q → ℂ) :
    (∑ y : ι → Q, ∏ i, g i (y i)) = ∏ i, ∑ w, g i w := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem trace_diag {Q : Type} [CommRing Q] (τ : Q →+* Q) (m n : ℕ) (d : Fin n → Q) (e : Fin m → Q)
    (y : Matrix (Fin m) (Fin n) Q) :
    Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)) =
      ∑ i, ∑ l, e l * d i * (τ (y l i) * y l i) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem red_diagonal {R : Type} [CommRing R] (ϖ : R) (k n : ℕ) (D : Fin n → R) :
    red ϖ k (Matrix.diagonal D) =
      Matrix.diagonal fun i => Ideal.Quotient.mk (lev ϖ k) (D i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [red]
  · simp [red, Matrix.diagonal_apply_ne _ h]

theorem sum_fun_prod {Q : Type} [Fintype Q] (m n : ℕ) (f : Fin n → Fin m → Q → ℂ) :
    (∑ y : Fin m → Fin n → Q, ∏ l, ∏ i, f i l (y l i)) = ∏ i, ∏ l, ∑ w, f i l w := by
  have h1 : ∀ l, ∑ v : Fin n → Q, ∏ i, f i l (v i) = ∏ i, ∑ w, f i l w := fun l =>
    sum_pi_prod (fun i => f i l)
  have h2 := sum_pi_prod (ι := Fin m) (Q := Fin n → Q) (fun l v => ∏ i, f i l (v i))
  simp only [h1] at h2
  rw [Finset.prod_comm]
  exact h2

theorem gauss_gen {Q : Type} [CommRing Q] [Fintype Q] (τ : Q →+* Q) (χ : AddChar Q ℂ) (m n : ℕ)
    (d : Fin n → Q) (e : Fin m → Q) :
    (∑ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Q, χ (e l * d i * (τ w * w)) := by
  let f : Fin n → Fin m → Q → ℂ := fun i l w => χ (e l * d i * (τ w * w))
  have hterm : ∀ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y))) =
        ∏ l, ∏ i, f i l (y l i) := by
    intro y
    rw [trace_diag, chi_sum, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chi_sum]
  exact (Fintype.sum_equiv Matrix.of.symm _ _ fun y => hterm y).trans (sum_fun_prod m n f)

theorem gauss_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  intro R _ σ ϖ hf k _ χ m n D E
  have h := gauss_gen (barσ σ ϖ hf k) χ m n (fun i => Ideal.Quotient.mk (lev ϖ k) (D i))
    (fun l => Ideal.Quotient.mk (lev ϖ k) (E l))
  simp only [red_diagonal, map_mul]
  exact h

end GlobalTheory.CompanionTheory.GaussProd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactorStatement

section

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.matrix_gauss_sum_diagonal_factor : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussProd.gauss_prod | exact GlobalTheory.CompanionTheory.GaussProd.gauss_prod | (intros; apply GlobalTheory.CompanionTheory.GaussProd.gauss_prod <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens

section

@[expose] public section

noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (R ⧸ lev ϖ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp [lev])
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using GlobalTheory.T.gauss_sum_hermitian_norm_level_one R σ ϖ q ε hR ψ hψ a ha ha'
  | more j ih _ =>
    rw [GlobalTheory.T.gauss_sum_hermitian_norm_level_shift R σ ϖ q ε hR ψ hψ j a ha ha', ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]
    ring

theorem gauss_full {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR m S hS.1
  have hq0 : (q : ℂ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  have hunit : ∀ l, e l ∉ lev ϖ 1 := by
    intro l hl
    have h1 : IsUnit p.det := Matrix.isUnit_det_of_right_inverse hpp
    have h2 : IsUnit (cT σ p).det := by
      have : cT σ p * cT σ p' = 1 := by
        have : cT σ (p' * p) = cT σ p * cT σ p' := by
          simp [cT, Matrix.transpose_mul, Matrix.map_mul]
        rw [← this, hpp']
        simp [cT]
      exact Matrix.isUnit_det_of_right_inverse this
    have h3 : IsUnit (Matrix.diagonal e).det := by
      rw [← hpe, Matrix.det_mul, Matrix.det_mul]
      exact (h2.mul hS.2).mul h1
    rw [Matrix.det_diagonal] at h3
    have h4 : IsUnit (e l) := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ l)) h3
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hl
    rw [hc, pow_one] at h4
    exact hR.notUnit (isUnit_of_mul_isUnit_left h4)
  choose eI heI hcard hsum using fun i => GlobalTheory.T.card_range_mul_quotient_bounded_level R σ ϖ q ε hR ψ hψ (fun j a ha ha' => gauss1 hR hψ hε j a ha ha') k (d i) (hd i)
  rw [GlobalTheory.T.matrix_gauss_sum_congr_invariance R σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    GlobalTheory.T.matrix_gauss_sum_diagonal_factor R σ ϖ hR.fix_ϖ k (ψ k) m n d e,
    GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd]
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hR.one_lt
  have hnu : (∏ i, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i))) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow hq2]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have hc : Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k
    have : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ k) = _
      rw [Nat.card_fun, Nat.card_fun, hc]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_mul, mul_comm n m]
    rw [this]; push_cast; rfl
  rw [hM]
  have hc' : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
    rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hc']
  simp only [fun i l => hsum i (e l) (he l) (hunit l), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, Finset.prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  have hx : ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x := fun x => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  rw [Finset.prod_pow_eq_pow_sum]

end GlobalTheory.CompanionTheory.SiegLoc
end
end
end
