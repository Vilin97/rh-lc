module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrixStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModificationStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheoremStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  first | exact @GlobalTheory.PMon.FrameEquiv.frameEx | exact GlobalTheory.PMon.FrameEquiv.frameEx | (intros; apply GlobalTheory.PMon.FrameEquiv.frameEx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.arith {α : Type} [Fintype α] [DecidableEq α] (f : α → ℤ) (h0 : ∑ z, f z = 0) (hf : f ≠ 0) :
    ∃ x y, x ≠ y ∧ ∑ z, (f z + eps x y z) = 0 ∧ ∑ z, (f z + eps x y z) ^ 2 < ∑ z, f z ^ 2 := by
  have hx : ∃ x, 0 < f x := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  have hy : ∃ y, f y < 0 := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x ≠ y := fun e => by rw [e] at hx; omega
  have e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x := by
    intro g
    have : ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0) := by
      intro z
      unfold eps
      by_cases a : z = x
      · subst a; simp [hxy]
      · by_cases b : z = y
        · subst b; simp [a]
        · simp [a, b]
    simp [this, Finset.sum_sub_distrib]
  have ex : eps x y x = -1 := by simp [eps]
  have ey : eps x y y = 1 := by simp [eps, hxy.symm]
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have := e1 fun _ => 1
    simp only [one_mul] at this
    rw [Finset.sum_add_distrib, h0, this]; simp
  · have a := e1 f
    have b := e1 (eps x y)
    have : ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, a, b, ex, ey]
    omega

theorem GlobalTheory.PMon.matThm_of_steps : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  intro hF hT hS hR hM l _ P AI T
  suffices H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N →
      ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from
    fun n _ _ K r ρ => H _ n rfl K r ρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro n _ _ hn K r ρ hρ hd
  obtain ⟨w, hw⟩ := (hF l P AI T n K r ρ hρ).1 hd
  obtain ⟨K', r', ρ', w', h1, h2, h3, h4⟩ := hT l P AI T n K r ρ w hρ hw
  apply h4
  suffices G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v →
      ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from
    G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl
  intro S
  induction S using Nat.strong_induction_on with
  | _ S IS =>
  intro σ v a1 a2 a3 a4
  by_cases hv : (fun z : Fin r' × n => v z.1 z.2) = 0
  · have : v = 0 := funext fun m => funext fun j => congrFun hv (m, j)
    subst this
    exact hS l P AI T n K' r' σ a1 a2
  by_cases hs : Splits r' σ
  · exact hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs
      fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2
  obtain ⟨x, y, hxy, c1, c2⟩ := GlobalTheory.PMon.arith _ a3 hv
  obtain ⟨τ, b1, b2, b3⟩ := hM l P AI T n K' r' σ v x y hxy a1 a2 hs
  refine b3 (IS _ ?_ τ _ b1 b2 c1 rfl)
  have p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S
  omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCasesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem matThm_holds : MatThm :=
  GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases GlobalTheory.T.deRham_iff_framed_galois_representation GlobalTheory.T.lubinTateTwistTotalWeightZero_proof GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem GlobalTheory.T.potentially_semistable_reducible_unramified_split GlobalTheory.T.monodromy_irreducible_elementary_weightModification

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixFormStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  first | exact @GlobalTheory.PMon.matThm_holds | exact GlobalTheory.PMon.matThm_holds | (intros; apply GlobalTheory.PMon.matThm_holds <;> assumption)
end
end
