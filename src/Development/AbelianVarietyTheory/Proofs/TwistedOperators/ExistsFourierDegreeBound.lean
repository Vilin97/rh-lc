module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Mathlib.Data.FunLike.Fintype
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfScalar

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

theorem mapDomain_fst_apply {ι κ : Type} [DecidableEq ι] (k : ι × κ →₀ ℕ) (τ : ι) :
    Finsupp.mapDomain Prod.fst k τ = ∑ v ∈ k.support with v.1 = τ, k v := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

def Mon (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Set (FVar D m n →₀ ℕ) := {k | Finsupp.mapDomain Prod.fst k = d}

open Classical in
theorem mon_finite (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : (Mon D m n d).Finite :=
  (GlobalTheory.finite_monomials_of_placeDegree D m n (fun τ => d τ)).subset fun k hk τ => by
    have e := mapDomain_fst_apply k τ
    rw [show Finsupp.mapDomain Prod.fst k = d from hk] at e
    convert e.symm

noncomputable instance (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Fintype (Mon D m n d) := (mon_finite D m n d).fintype

variable {D : D7}

def substMat (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g : GA D V) :
    Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ :=
  fun k' k => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (monomial k.1 1)) k'.1

open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

theorem eq_sum_mon {D : D7} {m n : ℕ} {d : D.what₂.Tau →₀ ℕ} (P : MvPolynomial (FVar D m n) ℂ)
    (hP : ∀ k', AddMonoidAlgebra.coeff P k' ≠ 0 → k' ∈ Mon D m n d) :
    P = ∑ k : Mon D m n d, AddMonoidAlgebra.coeff P k.1 • monomial k.1 (1 : ℂ) := by
  classical
  ext k'
  rw [coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k' ∈ Mon D m n d
  · rw [Finset.sum_eq_single ⟨k', hk⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h; exact hk (hP k' h)
    · intro b _; rw [if_neg]; rintro rfl; exact hk b.2

variable {D : D7}

theorem substMat_one (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) : substMat θ V m d 1 = 1 := by
  classical
  ext k' k
  simp only [substMat, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, substF_one, coeff_monomial, Matrix.one_apply]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

theorem one_alg (m : ℕ) (i : D.what₂.Tau) (a b : Fin m) :
    IsAlgebraic ℚ ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) i a b) := by
  by_cases hab : a = b
  · subst hab; show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a a); rw [Matrix.one_apply_eq]; exact isAlgebraic_one
  · show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a b); rw [Matrix.one_apply_ne hab]; exact isAlgebraic_zero

section Avg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem integral_expand (ρ : K → Matrix ι ι ℂ) (hρ : Continuous ρ) (Φ : ι → ℂ) (F : K → ℂ) (k : ι)
    (hF : ∀ g, F g = ∑ k', ρ g k' k * Φ k') : ∫ g, F g ∂κ = ∑ k', (∫ g, ρ g k' k ∂κ) * Φ k' := by
  simp_rw [hF]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k' _ => integral_mul_const _ _
  · exact fun k' _ => (GlobalTheory.HaarAlg.integrable_of_continuous κ (hρ.matrix_elem k' k)).mul_const _

theorem integral_eq_zero_of_scalar [κ.IsMulLeftInvariant] (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (z : K) (c : ℂ)
    (hc : c ≠ 1) (hz : ρ z = c • 1) (a b : ι) : ∫ g, ρ g a b ∂κ = 0 := by
  classical
  have h := GlobalTheory.HaarAlg.rho_mul_avg κ ρ hρ z
  rw [hz, Matrix.smul_mul, Matrix.one_mul] at h
  have h3 := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.HaarAlg.avg, Matrix.of_apply] at h3
  have h2 : (c - 1) * ∫ g, ρ g a b ∂κ = 0 := by rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)

end Avg

end GlobalTheory.RealAvg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMulStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by
  first | exact @GlobalTheory.CompactHowe.substF_mul | exact GlobalTheory.CompactHowe.substF_mul | (intros; apply GlobalTheory.CompactHowe.substF_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomial

section

@[expose] public section

noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomialStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial : ∀ {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ), GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  first | exact @GlobalTheory.CompactHowe.substF_scalar_monomial | exact GlobalTheory.CompactHowe.substF_scalar_monomial | (intros; apply GlobalTheory.CompactHowe.substF_scalar_monomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierDegreeBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

variable {D : D7}

theorem substMat_mul (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g₁ g₂ : GA D V) :
    substMat θ V m d (g₁ * g₂) = substMat θ V m d g₁ * substMat θ V m d g₂ := by
  ext k' k
  simp only [substMat, Matrix.mul_apply]
  have e : (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) =
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁)) * (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) :=
    funext fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_mul θ τ V g₁ g₂
  have e1 : (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) = (fun _ => 1) * (fun _ => 1) := by
    funext τ; simp
  have e2 : GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) (monomial k.1 1) =
      GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
        (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁))
        (GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
          (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) (monomial k.1 1)) := by
    rw [GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul, ← e, ← e1]
  rw [e2]
  conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
    (fun k'' h => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ h).trans k.2)]

  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun k'' _ => ?_
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem substMat_cont {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) :
    Continuous (fun g : GinfC V => substMat θ V m d g.1 k' k) := by
  have hc := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).1
  have hm : Continuous fun g : GinfC V => (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1)) :=
    continuous_pi fun τ =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val)
  have hp : Continuous fun g : GinfC V => ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)),
      (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1))) := continuous_const.prodMk hm
  have := hc.comp hp
  exact this

theorem substMat_alg (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) (g : GA D V) (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g) a b)) :
    IsAlgebraic ℚ (substMat θ V m d g k' k) := by
  have ha := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).2
    (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (one_alg m) hg
  exact ha

theorem substMat_central (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (z : GA D V) (τ₀ : D.what₂.Tau) (ζ : ℂ)
    (h1 : compAt θ τ₀ (Formalism.L2.Theta.mt V z) = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h2 : ∀ ρ, ρ ≠ τ₀ → compAt θ ρ (Formalism.L2.Theta.mt V z) = 1) :
    substMat θ V m d z = (ζ ^ d τ₀) • (1 : Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ) := by
  classical
  have e : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V z)) =
      fun ρ => if ρ = τ₀ then ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
    funext ρ
    by_cases hρ : ρ = τ₀
    · subst hρ; rw [if_pos rfl, h1]
    · rw [if_neg hρ, h2 ρ hρ]
  ext k' k
  simp only [substMat, e, GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial, MvPolynomial.coeff_smul, coeff_monomial, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [show Finsupp.mapDomain Prod.fst k.1 = d from k.2]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

end GlobalTheory.RealAvg

namespace GlobalTheory.RealAvg

open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)

end GlobalTheory.RealAvg
end
end
end
