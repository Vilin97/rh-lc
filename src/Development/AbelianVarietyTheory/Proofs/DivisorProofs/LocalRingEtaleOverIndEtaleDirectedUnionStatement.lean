module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnion
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOverDirectedUnionEssEtaleLocalStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnionStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.annihilator_of_directed_essentiallyEtale_union : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  first | exact @GlobalTheory.ann_of_directed_essEtale | exact GlobalTheory.ann_of_directed_essEtale | (intros; apply GlobalTheory.ann_of_directed_essEtale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationSubalgebraFrac

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem localization_subalgebra_frac :
  ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (C : Subalgebra R B), (∀ c ∈ C, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C, s ∉ Q ∧ s * c = 0) → ∃ V : Subalgebra R (Localization.AtPrime Q), (∀ x : Localization.AtPrime Q, x ∈ V ↔ ∃ a ∈ C, ∃ s ∈ C, s ∉ Q ∧ x * algebraMap B (Localization.AtPrime Q) s = algebraMap B (Localization.AtPrime Q) a) ∧ Nonempty (Localization.AtPrime (Q.comap (C.val : C →ₐ[R] B)) ≃ₐ[R] V) := by
  intro R B _ _ _ Q _ C hann
  set P : Ideal C := Q.comap (C.val : C →ₐ[R] B) with hP
  let φ0 : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (C.val : C →+* B) rfl
  have hmk : ∀ (c : C) (s : P.primeCompl), φ0 (IsLocalization.mk' _ c s) =
      IsLocalization.mk' (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl) := by
    intro c s
    exact Localization.localRingHom_mk' P Q (C.val : C →+* B) rfl c s
  let φ : Localization.AtPrime P →ₐ[R] Localization.AtPrime Q :=
    { φ0 with
      commutes' := by
        intro r
        have h1 : algebraMap R (Localization.AtPrime P) r = algebraMap C (Localization.AtPrime P) (algebraMap R C r) :=
          IsScalarTower.algebraMap_apply R C _ r
        have h2 := Localization.localRingHom_to_map P Q (C.val : C →+* B) rfl (algebraMap R C r)
        show φ0 (algebraMap R (Localization.AtPrime P) r) = _
        rw [h1, h2, IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q) r]
        rfl }
  have hφ : ∀ x, φ x = φ0 x := fun _ => rfl
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [hφ, hmk, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htc⟩ := hx
    obtain ⟨s', hs'C, hs'Q, hs'c⟩ := hann c c.2 t ht htc
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨⟨s', hs'C⟩, hs'Q⟩, ?_⟩
    apply Subtype.ext
    simpa using hs'c
  refine ⟨φ.range, ?_, ⟨(AlgEquiv.ofInjective φ hinj)⟩⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    refine ⟨c, c.2, (s : C), (s : C).2, s.2, ?_⟩
    show φ0 (IsLocalization.mk' (Localization.AtPrime P) c s) * _ = _
    rw [hmk]
    exact IsLocalization.mk'_spec (Localization.AtPrime Q) (c : B) (⟨(s : C), s.2⟩ : Q.primeCompl)
  · rintro ⟨a, ha, s, hs, hsQ, hx⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) (⟨a, ha⟩ : C) (⟨⟨s, hs⟩, hsQ⟩ : P.primeCompl), ?_⟩
    show φ0 _ = x
    rw [hmk]
    symm
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationSubalgebraFracStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_subalgebra_atPrime_fractions_equiv : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (C : Subalgebra R B), (∀ c ∈ C, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C, s ∉ Q ∧ s * c = 0) → ∃ V : Subalgebra R (Localization.AtPrime Q), (∀ x : Localization.AtPrime Q, x ∈ V ↔ ∃ a ∈ C, ∃ s ∈ C, s ∉ Q ∧ x * algebraMap B (Localization.AtPrime Q) s = algebraMap B (Localization.AtPrime Q) a) ∧ Nonempty (Localization.AtPrime (Q.comap (C.val : C →ₐ[R] B)) ≃ₐ[R] V) := by
  first | exact @GlobalTheory.localization_subalgebra_frac | exact GlobalTheory.localization_subalgebra_frac | (intros; apply GlobalTheory.localization_subalgebra_frac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationDirectedUnionEssEtaleLocal

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem localDecomp_core : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  intro R B _ _ _ Q _ ι _ _ _ C hC hcov hét hann
  have hV := fun i => GlobalTheory.T.exists_subalgebra_atPrime_fractions_equiv R B Q (C i) (hann i)
  choose V hVmem hVeq using hV
  refine ⟨ι, inferInstance, inferInstance, inferInstance, V, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem i x).1 hx
    exact (hVmem j x).2 ⟨a, hC hij ha, s, hC hij hs, hsQ, hxs⟩
  · intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨i1, h1⟩ := hcov a
    obtain ⟨i2, h2⟩ := hcov (s : B)
    obtain ⟨k, hk1, hk2⟩ := directed_of (· ≤ ·) i1 i2
    exact ⟨k, (hVmem k _).2 ⟨a, hC hk1 h1, s, hC hk2 h2, s.2, IsLocalization.mk'_spec _ _ _⟩⟩
  · intro m x hx hu
    obtain ⟨a, ha, s, hs, hsQ, hxs⟩ := (hVmem m x).1 hx
    have hsu : IsUnit (algebraMap B (Localization.AtPrime Q) s) :=
      IsLocalization.map_units _ (⟨s, hsQ⟩ : Q.primeCompl)
    have hau : IsUnit (algebraMap B (Localization.AtPrime Q) a) := hxs ▸ hu.mul hsu
    have haQ : a ∉ Q := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q a).1 hau
    refine ⟨↑hu.unit⁻¹, (hVmem m _).2 ⟨s, hs, a, ha, haQ, ?_⟩, hu.mul_val_inv⟩
    calc (↑hu.unit⁻¹ : Localization.AtPrime Q) * algebraMap B _ a
        = ↑hu.unit⁻¹ * (x * algebraMap B _ s) := by rw [hxs]
      _ = algebraMap B _ s := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  · intro m
    obtain ⟨A, i1, i2, i3, q, i4, ⟨e⟩⟩ := hét m
    obtain ⟨f⟩ := hVeq m
    exact ⟨A, i1, i2, i3, q, i4, ⟨e.trans f⟩⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationDirectedUnionEssEtaleLocalStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.localization_directedUnion_essEtale_local : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  first | exact @GlobalTheory.localDecomp_core | exact GlobalTheory.localDecomp_core | (intros; apply GlobalTheory.localDecomp_core <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnion

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem localDecomp_indEtale : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∀ (U : Subalgebra S T) (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [Q.IsPrime], Nonempty (Localization.AtPrime Q ≃ₐ[S] U) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ U.restrictScalars R) ∧ (∀ x ∈ U, ∃ m, x ∈ V m) ∧ (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
  intro R S T _ _ _ _ _ _ _ hS U B _ _ _ Q _ hf
  obtain ⟨f⟩ := hf
  letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, _, _, _, C, hCm, hCc, hCe⟩ := GlobalTheory.T.etale_over_directedUnion_essEtale_local R S B hS
  have hCe' : ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B)))) :=
    fun i => hCe i _ inferInstance
  have hann := GlobalTheory.T.annihilator_of_directed_essentiallyEtale_union R B Q ι C hCm hCc hCe'
  obtain ⟨μ, _, _, _, W, hWm, hWc, hWu, hWe⟩ := GlobalTheory.T.localization_directedUnion_essEtale_local R B Q ι C hCm hCc hCe' hann
  let g : Localization.AtPrime Q →ₐ[R] T :=
    { toRingHom := U.val.toRingHom.comp f.toRingHom
      commutes' := fun r => by
        show ((f (algebraMap R _ r) : U) : T) = algebraMap R T r
        rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q), f.commutes,
          IsScalarTower.algebraMap_apply R S T]
        rfl }
  have hg : ∀ x, g x = ((f x : U) : T) := fun _ => rfl
  have hinj : Function.Injective g := fun x y h => f.injective (Subtype.ext (by simpa [hg] using h))
  refine ⟨μ, inferInstance, inferInstance, inferInstance, fun m => (W m).map g, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n h => Subalgebra.map_mono (hWm h)
  · rintro m x ⟨w, -, rfl⟩
    exact (f w).2
  · intro x hx
    obtain ⟨m, hm⟩ := hWc (f.symm ⟨x, hx⟩)
    exact ⟨m, f.symm ⟨x, hx⟩, hm, by simp [hg]⟩
  · rintro m x ⟨w, hw, rfl⟩ y hy hxy
    have h1 : f w * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa [hg] using hxy)
    have hu : IsUnit w := by
      have h2 : w * f.symm ⟨y, hy⟩ = 1 := by apply f.injective; simpa using h1
      exact ⟨⟨w, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    obtain ⟨z, hz, hwz⟩ := hWu m w hw hu
    exact ⟨g z, ⟨z, hz, rfl⟩, by show g w * g z = 1; rw [← map_mul, hwz, map_one]⟩
  · intro m
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hWe m
    exact ⟨A, inferInstance, inferInstance, inferInstance, q, inferInstance,
      ⟨e.trans (Subalgebra.equivMapOfInjective (W m) g hinj)⟩⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnionStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.localRing_etale_over_indEtale_directedUnion : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∀ (U : Subalgebra S T) (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [Q.IsPrime], Nonempty (Localization.AtPrime Q ≃ₐ[S] U) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ U.restrictScalars R) ∧ (∀ x ∈ U, ∃ m, x ∈ V m) ∧ (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
  first | exact @GlobalTheory.localDecomp_indEtale | exact GlobalTheory.localDecomp_indEtale | (intros; apply GlobalTheory.localDecomp_indEtale <;> assumption)
end
end
