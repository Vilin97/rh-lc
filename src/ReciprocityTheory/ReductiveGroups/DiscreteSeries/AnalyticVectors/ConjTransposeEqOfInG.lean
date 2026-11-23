module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InPApplyEqZero

section

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qh16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inG :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      X.conjTranspose * UpperTheory.Reformulated.B.Qh16.Jm ε + UpperTheory.Reformulated.B.Qh16.Jm ε * X = (0 : Matrix (Fin n) (Fin n) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inP :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      UpperTheory.Reformulated.B.Qh16.inG ε X ∧ X * UpperTheory.Reformulated.B.Qh16.Jm ε = -(UpperTheory.Reformulated.B.Qh16.Jm ε * X)

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

section

@[expose] public section

noncomputable section

open Finset

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs with h <;> simp [h]

private theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_right_inv (Jm_mul_Jm ε)

private theorem isUnit_Jm (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_Jm ε, Jm_mul_Jm ε⟩, rfl⟩

private theorem conjTranspose_eq_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm, mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, neg_mul]

theorem exp_smul_mem_UJset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  have hc : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, conjTranspose_eq_of_inG hX, Jm_inv]
    simp
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ (isUnit_Jm ε), Jm_inv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Jm ε * _) (Jm ε) (Jm ε), Jm_mul_Jm, mul_one, mul_assoc]
    _ = Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem exp_add_smul (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

theorem exp_mem_Kset {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    NormedSpace.exp Z ∈ Kset ε := by
  have hZh : Zᴴ = -Z := by
    rw [conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1
    rw [← Matrix.exp_conjTranspose, hZh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)

theorem inP_apply_eq_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    {a b : Fin n} (hab : ε a = ε b) : X a b = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero .. | (apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> first | assumption | infer_instance)

theorem inK_apply_eq_zero {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {a b : Fin n} (hab : ε a ≠ ε b) : Z a b = 0 := by
  have h := congrFun (congrFun hZ.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  all_goals first
    | exact absurd (ha.trans hb.symm) hab
    | (simp [ha, hb] at h; first | linear_combination h / 2 | linear_combination -h / 2)

end ReciprocityTheory.ChartRestriction.DS
end
end
end
