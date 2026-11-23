module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EigenvectorsSumZeroEqZero

section

@[expose] public section

namespace UpperTheory.Reformulated.B.P6.r14a

theorem eigenvectors_sum_zero_eq_zero {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) :
    ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hsum a ha
    by_cases hall : ∀ b ∈ s, b = a
    · have h1 : ∑ i ∈ s, v i = v a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        exact absurd (hall b hb) hba
      rw [← h1]
      exact hsum
    · push_neg at hall
      obtain ⟨b, hb, hba⟩ := hall
      have hfb : f b ≠ f a := fun h => hba (hf h)
      obtain ⟨k, hk⟩ : ∃ k, f b k ≠ f a k := Function.ne_iff.mp hfb
      have hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i)
          = f i k' • ((f i k - f a k) • v i) := by
        intro i hi k'
        rw [map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]
      have h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0 := by
        have h3 : ∑ i ∈ s, (f i k - f a k) • v i
            = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi k, sub_smul]
        rw [h3, hsum, map_zero, smul_zero, sub_zero]
      have hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0 := by
        have h4 := Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha
        simp only [sub_self, zero_smul, add_zero] at h4
        rw [h4]
        exact h2
      have hw0 := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun i => (f i k - f a k) • v i) hw_eig hw_sum
      have hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0 := by
        intro i hi hne
        have hia : i ≠ a := fun h => hne (by rw [h])
        have h5 : (f i k - f a k) • v i = 0 := hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)
        rcases smul_eq_zero.mp h5 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      have hts : s.filter (fun i => f i k = f a k) ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩
      have hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0 := by
        rw [Finset.sum_filter_of_ne]
        · exact hsum
        · intro i hi hvi
          by_contra hne
          exact hvi (hz i hi hne)
      exact ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩)

theorem GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec :
    ∀ {ι κ A : Type} [DecidableEq ι] [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] (T : κ → Module.End ℂ A) (f : ι → κ → ℂ), Function.Injective f → ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ (k : κ), DFunLike.coe (T k) (v i) = f i k • v i) → ∑ i ∈ s, v i = OfNat.ofNat (nat_lit 0) → ∀ i ∈ s, v i = OfNat.ofNat (nat_lit 0) := by
  intro ι κ A _ _ _ T f hf s v hv hsum
  exact eigenvectors_sum_zero_eq_zero T f hf s v hv hsum

end UpperTheory.Reformulated.B.P6.r14a
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectors

section

@[expose] public section

noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add (f := _), map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)

      simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement

section

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
end
end
