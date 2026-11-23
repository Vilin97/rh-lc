module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementG
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Ultra

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

theorem sum_sum_prod_two {K : Type} [CommRing K] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
    (A : J₁ → J₁ → K) (B : J₂ → J₂ → K) :
    ∑ j : J₁ × J₂, ∑ k : J₁ × J₂, A j.1 k.1 * B j.2 k.2 =
      (∑ a, ∑ a', A a a') * (∑ l, ∑ l', B l l') := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem sum_sum_prod_three {K : Type} [CommRing K] {J₁ J₂ J₃ : Type} [Fintype J₁] [Fintype J₂] [Fintype J₃]
    (A : J₁ → J₁ → K) (B : J₂ → J₂ → K) (C : J₃ → J₃ → K) :
    ∑ j : J₁ × J₂ × J₃, ∑ k : J₁ × J₂ × J₃, A j.1 k.1 * (B j.2.1 k.2.1 * C j.2.2 k.2.2) =
      (∑ a, ∑ a', A a a') * ((∑ l, ∑ l', B l l') * (∑ r, ∑ r', C r r')) := by
  rw [sum_sum_prod_two A (fun j k : J₂ × J₃ => B j.1 k.1 * C j.2 k.2), sum_sum_prod_two B C]

theorem tripleTensorAlmostOrthonormal : TensorBlock := by
  intro K _ _ E _ H _ _ emb Ja Jl Jr _ _ _ hA hl hr N0 N1 Gc P P' th u hth hvan hu hun hL hR t ab ab'
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := ab'
  obtain ⟨e₁, he₁, hE₁⟩ := hL t a a'
  obtain ⟨e₂, he₂, hE₂⟩ := hR t b b'

  have hsep : ∑ j : Ja × Jl × Jr, ∑ k : Ja × Jl × Jr,
        (Gc (false, t) j.1 * P (false, t) j.2.1 a * P' (false, t) j.2.2 b) *
          (∑ ρ : Bool × H, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) *
          (Gc (true, t) k.1 * P (true, t) k.2.1 a' * P' (true, t) k.2.2 b') =
      ∑ ρ : Bool × H, (∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α') *
        ((∑ l, ∑ l₂, P (false, t) l a * emb ρ (hl l l₂) * P (true, t) l₂ a') *
          (∑ r, ∑ r₂, P' (false, t) r b * emb ρ (hr r r₂) * P' (true, t) r₂ b')) := by
    simp_rw [← sum_sum_prod_three]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_mul, map_mul]
    ring
  have hzero : ∀ ρ : Bool × H, ρ ≠ (false, t) →
      ∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α' = 0 := by
    intro ρ hρ
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α' _ => ?_
    rw [← Finset.sum_mul, hvan (false, t) ρ hρ α', zero_mul]
  have hsingle : ∑ ρ : Bool × H, (∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α') *
        ((∑ l, ∑ l₂, P (false, t) l a * emb ρ (hl l l₂) * P (true, t) l₂ a') *
          (∑ r, ∑ r₂, P' (false, t) r b * emb ρ (hr r r₂) * P' (true, t) r₂ b')) =
      u t * ((((if a = a' then 1 else 0) + th * e₁)) * ((if b = b' then 1 else 0) + th * e₂)) := by
    rw [Finset.sum_eq_single (false, t) (fun ρ _ hρ => by rw [hzero ρ hρ, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), ← hu t, hE₁, hE₂]
  have hda : ‖(if a = a' then (1 : K) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have hdb : ‖(if b = b' then (1 : K) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have mul1 : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := by
    intro x y hx hy
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  have add1 : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x + y‖ ≤ 1 := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  refine ⟨u t * ((if a = a' then (1 : K) else 0) * e₂ + e₁ * (if b = b' then (1 : K) else 0) + th * (e₁ * e₂)), ?_, ?_⟩
  · exact mul1 _ _ (hun t) (add1 _ _ (add1 _ _ (mul1 _ _ hda he₂) (mul1 _ _ he₁ hdb))
      (mul1 _ _ hth (mul1 _ _ he₁ he₂)))
  · show ∑ j : Ja × Jl × Jr, ∑ k : Ja × Jl × Jr,
        (Gc (false, t) j.1 * P (false, t) j.2.1 a * P' (false, t) j.2.2 b) *
          (∑ ρ : Bool × H, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) *
          (Gc (true, t) k.1 * P (true, t) k.2.1 a' * P' (true, t) k.2.2 b') = _
    rw [hsep, hsingle]
    have hif : (if (a, b) = (a', b') then u t else 0) =
        u t * ((if a = a' then (1 : K) else 0) * (if b = b' then (1 : K) else 0)) := by
      by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [Prod.mk.injEq, h1, h2]
    rw [hif]
    ring

end Formalism.L2.Th1.GD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRoot

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem GlobalTheory.DFrame.pairedBlock_diag : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  intro D p _ ι X s L sc n N N' a cκ r P P' σ σ' th hth hOK hvan hu hL hR t ab ab'
  obtain ⟨e, he, hE⟩ := Formalism.L2.Th1.GD.tripleTensorAlmostOrthonormal ℂ_[p] D.host.E (HH D) (GlobalTheory.DFrame.rho D ι)
    (Σ z : Bool × HH D, Fin (n z)) ((Bool × HH D) × Fin N) ((Bool × HH D) × Fin N')
    (fun α α' => a α.1 α.2 * D.host.conj (a α'.1 α'.2))
    (fun (l l₂ : (Bool × HH D) × Fin N) => ∑ j : Fin N, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j))
    (fun (q q₂ : (Bool × HH D) × Fin N') => ∑ i : Fin N', GlobalTheory.DFrame.colR D P' σ' q i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' q₂ i))
    N N' (GlobalTheory.DFrame.gc D cκ r) (GlobalTheory.DFrame.pc D ι σ) (GlobalTheory.DFrame.pc D ι σ') th
    (GlobalTheory.DFrame.uu D ι cκ r a) hth hvan (fun _ => rfl) hu hL hR t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← hE]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hOK]
  unfold GlobalTheory.DFrame.coef
  congr 2
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  simp only [GlobalTheory.DFrame.mat, Matrix.of_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRootStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualFrame_paired_blocks_diagonal_mod_root : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  first | exact @GlobalTheory.DFrame.pairedBlock_diag | exact GlobalTheory.DFrame.pairedBlock_diag | (intros; apply GlobalTheory.DFrame.pairedBlock_diag <;> assumption)
end
end
