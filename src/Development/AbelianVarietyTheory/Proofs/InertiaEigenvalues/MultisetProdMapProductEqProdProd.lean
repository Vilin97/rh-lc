module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegreeStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSubStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOne

section

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

open PowerSeries

theorem hasSum_coeff_mk_mul_polynomial (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (p : Polynomial ℂ) :
    HasSum (fun d => coeff d (mk c * (p : PowerSeries ℂ))) ((∑' d, c d) * p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [Polynomial.coe_add, mul_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    have hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)))
        = fun d => if n ≤ d then c (d - n) * a else 0 := by
      funext d
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc,
        PowerSeries.coeff_mul_X_pow']
      split_ifs <;> simp [PowerSeries.coeff_mul_C]
    rw [hf, Polynomial.eval_monomial, one_pow, mul_one]
    refine (hasSum_nat_add_iff' n).mp ?_
    have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [not_le.mpr hi]
    rw [h0, sub_zero]
    simpa using (Summable.of_norm hc).hasSum.mul_right a

theorem eulerInverse_eval_one {ι : Type} [Fintype ι] (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (Q : ι → ℂ)
    (h : PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1) :
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef
  have hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ
    rw [hPdef]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
    rw [this]
    simp
  have h1 := hasSum_coeff_mk_mul_polynomial c hc P
  rw [hP, h] at h1
  have h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1 := by
    simpa [PowerSeries.coeff_one] using hasSum_ite_eq 0 (1 : ℂ)
  have h3 := h1.unique h2
  have hev : P.eval 1 = ∏ p, (1 - Q p) := by simp [hPdef, Polynomial.eval_prod]
  rw [hev] at h3
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [← eq_inv_of_mul_eq_one_left h3]
    exact (Summable.of_norm hc).hasSum

end GlobalTheory.JSW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOneStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  exact @GlobalTheory.JSW.eulerInverse_eval_one
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree

section

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

end GlobalTheory.JSW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegreeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  first | exact @GlobalTheory.JSW.regroup_antiParts | exact GlobalTheory.JSW.regroup_antiParts | (intros; apply GlobalTheory.JSW.regroup_antiParts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd

section

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

open Finset

theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← GlobalTheory.T.cauchy_identity_schur_formal_degree hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
end
end
end
