module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisation
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulOfSurjective
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHenselisationStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_etale_localization_filtration_henselization : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.Henselisation.exists_henselisation | exact GlobalTheory.Henselisation.exists_henselisation | (intros; apply GlobalTheory.Henselisation.exists_henselisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlat

section

@[expose] public section

open TensorProduct LinearMap

namespace GlobalTheory

theorem flat_of_forall_finset_subset_flat :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
      (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) →
        Module.Flat R M := by
  intro R M _ _ _ h
  refine Module.Flat.iff_lTensor_injective'.mpr fun I => ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨J, hfg, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R) (M := ↥I) x
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨N, hsN, hN⟩ := h s
  have hJN : J ≤ N := hs ▸ Submodule.span_le.mpr hsN
  obtain ⟨y', hy'⟩ : ∃ y' : ↥N ⊗[R] ↥I, y' = rTensor (↥I) (Submodule.inclusion hJN) y := ⟨_, rfl⟩
  have hxy : rTensor (↥I) J.subtype y = rTensor (↥I) N.subtype y' := by
    rw [hy', ← rTensor_comp_apply]; rfl
  rw [hxy] at hx ⊢
  have hcomm : lTensor M I.subtype (rTensor (↥I) N.subtype y') =
      rTensor R N.subtype (lTensor (↥N) I.subtype y') := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor, rTensor_comp_lTensor]
  rw [hcomm] at hx
  have hinj1 : Function.Injective (rTensor R N.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) N.subtype Subtype.val_injective
  have h0 : lTensor (↥N) I.subtype y' = 0 := hinj1 (by rw [hx, map_zero])
  have hinj2 : Function.Injective (lTensor (↥N) I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ↥N) I.subtype Subtype.val_injective
  have : y' = 0 := hinj2 (by rw [h0, map_zero])
  rw [this, map_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlatStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) → Module.Flat R M := by
  first | exact @GlobalTheory.flat_of_forall_finset_subset_flat | exact GlobalTheory.flat_of_forall_finset_subset_flat | (intros; apply GlobalTheory.flat_of_forall_finset_subset_flat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselian

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

open StrictHensOfHens

theorem exists_strictHenselisation_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ _
  have hflat : Module.Flat R (SH R Ω) := by
    refine GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule R (SH R Ω) fun s => ?_
    obtain ⟨E, hE⟩ := StrictHensOfHens.exists_ofA_finset (R := R) (Ω := Ω) s
    let e := AlgEquiv.ofInjective (ofA (R := R) (Ω := Ω) E) (ofA_injective E)
    haveI : Module.Flat R (Lift R Ω E) := Algebra.Smooth.flat _ _
    refine ⟨Subalgebra.toSubmodule (ofA (R := R) (Ω := Ω) E).range, fun x hx => ?_,
      Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩
    obtain ⟨a, rfl⟩ := hE x hx
    exact ⟨a, rfl⟩
  refine ⟨SH R Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    isSepClosed_residueField, hflat, map_maximalIdeal, ⟨resAlgEquiv⟩, Idx R Ω, inferInstance,
    inferInstance, inferInstance, fun E => (ofA (R := R) (Ω := Ω) E).range, ?_, ?_, fun E => ?_⟩
  · intro E F h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨trans R Ω E F h a, ofA_trans h a⟩
  · intro s
    obtain ⟨E, a, rfl⟩ := StrictHensOfHens.exists_ofA (R := R) (Ω := Ω) s
    exact ⟨E, a, rfl⟩
  · refine ⟨Lift R Ω E, inferInstance, inferInstance, inferInstance, maximalIdeal _, inferInstance, ⟨?_⟩⟩
    have hu : (maximalIdeal (Lift R Ω E)).primeCompl ≤ IsUnit.submonoid (Lift R Ω E) :=
      fun x hx => by simpa [IsUnit.mem_submonoid_iff, mem_maximalIdeal, mem_nonunits_iff] using hx
    exact ((IsLocalization.atUnits (Lift R Ω E) (maximalIdeal (Lift R Ω E)).primeCompl
      (S := Localization.AtPrime (maximalIdeal (Lift R Ω E))) hu).restrictScalars R).symm.trans
      (AlgEquiv.ofInjective (ofA (R := R) (Ω := Ω) E) (ofA_injective E))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselianStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_etale_localization_filtration_strictHenselization : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.exists_strictHenselisation_of_henselian | exact GlobalTheory.exists_strictHenselisation_of_henselian | (intros; apply GlobalTheory.exists_strictHenselisation_of_henselian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTransStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.indEtale_localizedPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.indEtale_localPieces_trans | exact GlobalTheory.indEtale_localPieces_trans | (intros; apply GlobalTheory.indEtale_localPieces_trans <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem exists_strictHenselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ hΩ
  obtain ⟨H, _, _, _, _, hflat, hmax, hbij, hind⟩ := GlobalTheory.T.exists_etale_localization_filtration_henselization R
  let e : ResidueField R ≃+* ResidueField H := RingEquiv.ofBijective _ hbij
  letI algH : Algebra (ResidueField H) Ω :=
    ((algebraMap (ResidueField R) Ω).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (ResidueField H) Ω).comp e.toRingHom =
      (RingEquiv.refl Ω : Ω →+* Ω).comp (algebraMap (ResidueField R) Ω) := by
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  haveI : IsSepClosure (ResidueField H) Ω :=
    ⟨hΩ.sep_closed, Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ω) he⟩
  obtain ⟨T, _, _, _, _, hsc, hflat2, hmax2, ⟨e2⟩, hind2⟩ := GlobalTheory.T.exists_etale_localization_filtration_strictHenselization H Ω
  letI algRT : Algebra R T := ((algebraMap H T).comp (algebraMap R H)).toAlgebra
  haveI : IsScalarTower R H T := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalHom (algebraMap R T) := by
    change IsLocalHom ((algebraMap H T).comp (algebraMap R H))
    infer_instance
  refine ⟨T, inferInstance, algRT, inferInstance, hloc, hsc, ?_, ?_, ?_, ?_⟩
  · haveI := hflat; haveI := hflat2
    exact Module.Flat.trans R H T
  · rw [IsScalarTower.algebraMap_eq R H T, ← Ideal.map_map, hmax, hmax2]
  · refine ⟨{ e2 with commutes' := ?_ }⟩
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    have h1 : algebraMap (ResidueField R) (ResidueField T) (residue R x) =
        algebraMap (ResidueField H) (ResidueField T) (residue H (algebraMap R H x)) := by
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue]; rfl
    have h2 : algebraMap (ResidueField H) Ω (residue H (algebraMap R H x)) =
        algebraMap (ResidueField R) Ω (residue R x) := by
      rw [RingHom.algebraMap_toAlgebra]
      simp only [RingHom.comp_apply]
      congr 1
      apply e.symm_apply_eq.mpr
      rfl
    show e2 (algebraMap (ResidueField R) (ResidueField T) (residue R x)) = _
    rw [h1, AlgEquiv.commutes, h2]
  · exact GlobalTheory.T.indEtale_localizedPieces_trans R H T hind hind2

end GlobalTheory
end
end
