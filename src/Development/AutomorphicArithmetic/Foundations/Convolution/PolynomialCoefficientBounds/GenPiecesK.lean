module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AevalSingleZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.CoeffL1NormNonneg
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.IntMvPolynomialCoeffAbsSumAddLe
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceHom

section

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_hom :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (k : ℕ), (piece k f).IsHomogeneous k := by
  intro ι _ f k
  have hlin : ∀ v : ι → ℝ, (lin v).IsHomogeneous 1 := fun v =>
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_C ι ((v i : ℝ) : ℂ)).mul (isHomogeneous_X ℂ i)
  unfold piece Finsupp.sum
  refine IsHomogeneous.sum _ _ _ fun v _ => IsHomogeneous.sum _ _ _ fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h := (homogeneousComponent_isHomogeneous (k - b) (f.coeff v)).mul
    ((isHomogeneous_C ι ((b.factorial : ℂ)⁻¹)).mul ((hlin v).pow b))
  have e : k - b + (0 + 1 * b) = k := by omega
  rwa [e] at h
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPieces

section

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.gen_pieces :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (f : EP (τ × Fin n)), (∀ w : τ → Equiv.Perm (Fin n), ren (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) f = f) → ∃ (K : ℝ) (G : ℕ → MvPolynomial (τ × Fin n) ℂ), ∀ k, aeval blockE (G k) = piece k f ∧ (G k).totalDegree ≤ k ∧ l1 (G k) ≤ K ^ (k + 1) / k.factorial := by
  intro τ _ _ n f hf
  have hgen : Generators := UpperTheory.ConvolutionTheory.FX.generators0
  obtain ⟨K₁, hK₁⟩ := hgen τ n
  obtain ⟨K₂, hK₂⟩ := UpperTheory.ConvolutionTheory.FX.piece_size (τ × Fin n) f
  have h : ∀ k, ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval blockE G = piece k f ∧ G.totalDegree ≤ k ∧
      l1 G ≤ K₁ ^ (k + 1) * l1 (piece k f) := fun k =>
    hK₁ k (piece k f) (UpperTheory.ConvolutionTheory.FX.piece_hom _ f k).totalDegree_le
      (fun w => by rw [← UpperTheory.ConvolutionTheory.FX.piece_ren, hf w])
  choose G hG using h
  refine ⟨|K₁| * K₂, G, fun k => ⟨(hG k).1, (hG k).2.1, ?_⟩⟩
  have h0 : 0 ≤ l1 (piece k f) := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc l1 (G k) ≤ K₁ ^ (k + 1) * l1 (piece k f) := (hG k).2.2
    _ ≤ |K₁| ^ (k + 1) * l1 (piece k f) := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        rw [← abs_pow]; exact le_abs_self _
    _ ≤ |K₁| ^ (k + 1) * (K₂ ^ (k + 1) / k.factorial) :=
        mul_le_mul_of_nonneg_left (hK₂ k) (by positivity)
    _ = (|K₁| * K₂) ^ (k + 1) / k.factorial := by rw [mul_pow]; ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPiecesK

section

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.gen_piecesK :
    ∀ (τ κ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (F : KF (τ × Fin n) κ), (∀ w : τ → Equiv.Perm (Fin n), map (ren (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2))) F = F) → ∃ (K : ℝ) (G : ℕ → MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)), ∀ k, map (aeval (blockE (τ := τ) (n := n)) : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ).toRingHom (G k) = pieceK k F ∧ (G k).support ⊆ F.support ∧ ∀ β, ((G k).coeff β).totalDegree ≤ k ∧ l1 ((G k).coeff β) ≤ K ^ (k + 1) / k.factorial := by
  intro τ κ _ _ n F hF
  classical
  have h : ∀ β : κ →₀ ℕ, ∃ (K : ℝ) (G : ℕ → MvPolynomial (τ × Fin n) ℂ), ∀ k,
      aeval blockE (G k) = piece k (F.coeff β) ∧ (G k).totalDegree ≤ k ∧
        l1 (G k) ≤ K ^ (k + 1) / k.factorial := fun β =>
    UpperTheory.ConvolutionTheory.FX.gen_pieces τ n (F.coeff β) (fun w => by
      have := congrArg (fun P => AddMonoidAlgebra.coeff P β) (hF w)
      simpa only [coeff_map] using this)
  choose K G hG using h
  have hc : ∀ k β, (∑ γ ∈ F.support, monomial γ (G γ k) :
      MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)).coeff β = if β ∈ F.support then G β k else 0 := by
    intro k β
    simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  have hK0 : 0 ≤ ∑ γ ∈ F.support, |K γ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ γ ∈ F.support, |K γ|, fun k => ∑ γ ∈ F.support, monomial γ (G γ k), fun k => ⟨?_, ?_, fun β => ?_⟩⟩

  · rw [map_sum, pieceK]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_monomial, ← (hG γ k).1]
    rfl
  · intro β hβ
    rw [mem_support_iff, hc] at hβ
    by_contra hn
    exact hβ (if_neg hn)
  · rw [hc]
    split_ifs with hβ
    · refine ⟨(hG β k).2.1, (hG β k).2.2.trans ?_⟩
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc K β ^ (k + 1) ≤ |K β| ^ (k + 1) := by rw [← abs_pow]; exact le_abs_self _
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _)
            (Finset.single_le_sum (f := fun γ => |K γ|) (fun _ _ => abs_nonneg _) hβ) _
    · refine ⟨by simp, ?_⟩
      have : l1 (0 : MvPolynomial (τ × Fin n) ℂ) = 0 := by simp [l1]
      rw [this]
      positivity
end
end
