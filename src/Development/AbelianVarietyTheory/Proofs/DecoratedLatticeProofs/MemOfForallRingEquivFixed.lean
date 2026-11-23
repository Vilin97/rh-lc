module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne

section

@[expose] public section

namespace GlobalTheory.ShiftVariables

noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)

theorem shiftVars_X (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental (↥k) c) :
    ∃ (σ : Ω ≃+* Ω), (∀ a ∈ k, (σ : Ω → Ω) a = a) ∧ (σ : Ω → Ω) c = c + (1 : Ω) := by
  classical
  have hs : AlgebraicIndepOn (↥k) id ({c} : Set Ω) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hc)
  obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset hs
  have hind : AlgebraicIndependent (↥k) ((↑) : t → Ω) := ht.1
  set K := IntermediateField.adjoin (↥k) (Set.range ((↑) : t → Ω)) with hK
  let e := hind.aevalEquivField
  let φ : FractionRing (MvPolynomial t ↥k) ≃ₐ[↥k] FractionRing (MvPolynomial t ↥k) :=
    IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial t ↥k))
      (L := FractionRing (MvPolynomial t ↥k)) (shiftVars t ↥k)
  let τ : K ≃ₐ[↥k] K := e.symm.trans (φ.trans e)
  have hmem : ∀ i : t, (i : Ω) ∈ K := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have he : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i)) = ⟨i, hmem i⟩ := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have he1 : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i + 1)) =
      ⟨i, hmem i⟩ + 1 := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have hτ : ∀ i : t, τ ⟨i, hmem i⟩ = ⟨i, hmem i⟩ + 1 := by
    intro i
    have h0 : e.symm ⟨i, hmem i⟩ = algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq, he]
    change e (φ (e.symm ⟨i, hmem i⟩)) = _
    rw [h0, IsFractionRing.algEquivOfAlgEquiv_algebraMap, shiftVars_X, he1]
  have : Algebra.IsAlgebraic K Ω := ht.isAlgebraic_field
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω τ.toRingEquiv
  have hσ : ∀ y : K, σ (y : Ω) = (τ y : Ω) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ.toRingEquiv y
  refine ⟨σ, fun a ha => ?_, ?_⟩
  · have hak : a ∈ K := IntermediateField.algebraMap_mem K (⟨a, ha⟩ : ↥k)
    have h1 := hσ ⟨a, hak⟩
    have h2 : τ ⟨a, hak⟩ = ⟨a, hak⟩ := τ.commutes (⟨a, ha⟩ : ↥k)
    rw [h2] at h1
    exact h1
  · have hc' : c ∈ t := hct rfl
    have h1 := hσ ⟨c, hmem ⟨c, hc'⟩⟩
    rw [hτ ⟨c, hc'⟩] at h1
    simpa using h1

end GlobalTheory.ShiftVariables
end
end

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField

section

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed

section

@[expose] public section

open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

end GlobalTheory.FixedRoots
end
end
