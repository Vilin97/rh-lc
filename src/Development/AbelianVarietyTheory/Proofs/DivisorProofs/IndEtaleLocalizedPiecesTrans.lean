module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnionStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirected

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem essEtaleLocal_le_of_directed :
  ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  classical
  intro R T _ _ _ U μ _ _ _ V hmono hcov hloc W hWU hW
  obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hW
  let L := Localization.AtPrime q
  let φ : A →ₐ[R] T := W.val.comp (e.toAlgHom.comp (IsScalarTower.toAlgHom R A L))
  have hφW : ∀ a, φ a ∈ W := fun a => (e (algebraMap A L a)).2
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  choose f hf using fun a : A => hcov (φ a) (hWU (hφW a))
  obtain ⟨M, hM⟩ := (s.image f).exists_le
  have hrange : ∀ a, φ a ∈ V M := by
    have hle : (⊤ : Subalgebra R A) ≤ (V M).comap φ := by
      rw [← hs]
      refine Algebra.adjoin_le ?_
      intro a ha
      exact hmono (hM _ (Finset.mem_image_of_mem f ha)) (hf a)
    intro a
    exact hle Algebra.mem_top
  refine ⟨M, fun w hw => ?_⟩
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨w, hw⟩)
  set y : T := ((e (IsLocalization.mk' L (1 : A) t) : W) : T) with hy
  have hyU : y ∈ U := hWU (e _).2
  have hxy : φ t * y = 1 := by
    have h1 : algebraMap A L t * IsLocalization.mk' L (1:A) t = 1 := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self']
    have h2 : ((e (algebraMap A L t * IsLocalization.mk' L (1:A) t) : W) : T) = 1 := by
      rw [h1, map_one]; rfl
    rw [map_mul, Subalgebra.coe_mul] at h2
    exact h2
  obtain ⟨z, hzV, hz⟩ := hloc M (φ t) (hrange t) y hyU hxy
  have hzy : z = y := by
    calc z = (y * φ t) * z := by rw [mul_comm y, hxy, one_mul]
      _ = y * (φ t * z) := by ring
      _ = y := by rw [hz, mul_one]
  have hw' : w = φ a * y := by
    have h1 : (⟨w, hw⟩ : W) = e (IsLocalization.mk' L a t) := by
      change IsLocalization.mk' L a t = _ at hat
      rw [hat, AlgEquiv.apply_symm_apply]
    have h2 : IsLocalization.mk' L a t = algebraMap A L a * IsLocalization.mk' L (1:A) t := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
    have h3 : w = ((e (IsLocalization.mk' L a t) : W) : T) := congrArg Subtype.val h1
    rw [h3, h2, map_mul, Subalgebra.coe_mul]
    rfl
  rw [hw', ← hzy]
  exact (V M).mul_mem (hrange a) hzV

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirectedStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_le_of_essEtaleLocal_directed : ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  first | exact @GlobalTheory.essEtaleLocal_le_of_directed | exact GlobalTheory.essEtaleLocal_le_of_directed | (intros; apply GlobalTheory.essEtaleLocal_le_of_directed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem indEtale_localPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R S T _ _ _ _ _ _ _ hS hT
  obtain ⟨κ, _, _, _, Tj, hmono, hcov, hpc⟩ := hT
  have hK : ∀ j, ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ)
      (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ (Tj j).restrictScalars R) ∧
      (∀ x ∈ Tj j, ∃ m, x ∈ V m) ∧
      (∀ m, ∀ x ∈ V m, ∀ y ∈ Tj j, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
    intro j
    obtain ⟨B, _, _, _, Q, _, ⟨e⟩⟩ := hpc j
    exact GlobalTheory.T.localRing_etale_over_indEtale_directedUnion R S T hS (Tj j) B Q ⟨e⟩
  choose μ pre dir ne V hVmono hVle hVcov hVloc hVee using hK
  let P : Subalgebra R T → Prop := fun W => ∃ (j : κ) (m : μ j), V j m = W
  have key : ∀ (j₁ : κ) (m₁ : μ j₁) (j : κ), j₁ ≤ j → ∃ m : μ j, V j₁ m₁ ≤ V j m := by
    intro j₁ m₁ j hj
    letI := pre j; haveI := dir j; haveI := ne j
    refine GlobalTheory.T.exists_le_of_essEtaleLocal_directed R T ((Tj j).restrictScalars R) (μ j) (V j) (hVmono j) ?_ ?_ (V j₁ m₁) ?_
      (hVee j₁ m₁)
    · intro x hx; exact hVcov j x hx
    · intro m x hx y hy hxy; exact hVloc j m x hx y hy hxy
    · intro x hx
      have := hVle j₁ m₁ hx
      exact hmono hj this
  refine ⟨{W : Subalgebra R T // P W}, inferInstance, ⟨?_⟩, ?_, Subtype.val, fun a b h => h, ?_, ?_⟩
  · rintro ⟨W₁, j₁, m₁, rfl⟩ ⟨W₂, j₂, m₂, rfl⟩
    obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁ j₂
    obtain ⟨a, ha⟩ := key j₁ m₁ j h₁
    obtain ⟨b, hb⟩ := key j₂ m₂ j h₂
    letI := pre j; haveI := dir j
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    exact ⟨⟨V j c, j, c, rfl⟩, ha.trans (hVmono j hac), hb.trans (hVmono j hbc)⟩
  · obtain ⟨j⟩ := (inferInstance : Nonempty κ)
    obtain ⟨m⟩ := ne j
    exact ⟨⟨V j m, j, m, rfl⟩⟩
  · intro t
    obtain ⟨j, hj⟩ := hcov t
    obtain ⟨m, hm⟩ := hVcov j t hj
    exact ⟨⟨V j m, j, m, rfl⟩, hm⟩
  · rintro ⟨W, j, m, rfl⟩
    exact hVee j m

end GlobalTheory
end
end
