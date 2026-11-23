module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIso
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExtendClassCoprimeEtaleExcisionStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIsoStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalExcisionBoundaryEtaleNbhd

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.NatRef

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1; simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_inr_map {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass (mappingCone φ₂) I n) :
    cpull (mappingCone.inr φ₁) I n (cpull (mappingCone.map φ₁ φ₂ a b comm) I n x) =
      cpull b I n (cpull (mappingCone.inr φ₂) I n x) := by
  rw [← cpull_comp, ← cpull_comp]
  congr 2
  simp [mappingCone.map]

theorem cpull_map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass K₂ I n) :
    cpull (mappingCone.map φ₁ φ₂ a b comm) I (n + 1) (cpre (mappingCone.fst φ₂) I n (n + 1) (by omega) x) =
      cpre (mappingCone.fst φ₁) I n (n + 1) (by omega) (cpull a I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  have key : (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
    refine (mappingCone.ext_cochain_from_iff φ₁ 0 1 rfl).2 ⟨?_, ?_⟩
    · rw [← Cochain.comp_assoc _ _ _ (show -1 + 0 = -1 by omega) (zero_add 1) (by omega), ← Cochain.comp_assoc _ _ _ (show -1 + 1 = 0 by omega) (add_zero 1) (by omega)]
      simp [mappingCone.map, Cochain.comp_assoc_of_second_is_zero_cochain]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain]
      simp [mappingCone.map, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, key, Cochain.comp_assoc_of_second_is_zero_cochain]

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC.NatRef
variable {R : Type} [CommRing R]

theorem abstract_nat {K L K' L' : Cx R} (φ : K ⟶ L) (φ' : K' ⟶ L') (a : K' ⟶ K) (b : L' ⟶ L)
    (comm : φ' ≫ b = a ≫ φ) (I : Cx R) (n : ℤ)
    (hbij : Function.Bijective (cpull (mappingCone.map φ' φ a b comm) I (n + 1))) :
    ∃ δ : CohomologyClass K' I n →+ CohomologyClass L I (n + 1),
      Function.Exact δ (fun x : CohomologyClass L I (n + 1) => (cpull φ I (n + 1) x, cpull b I (n + 1) x)) ∧
      ∀ {K₂ L₂ : Cx R} (φ₂ : K₂ ⟶ L₂) (a₂ : K₂ ⟶ K') (b₂ : L₂ ⟶ L') (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ')
        (a₃ : K₂ ⟶ K) (b₃ : L₂ ⟶ L) (comm₃ : φ₂ ≫ b₃ = a₃ ≫ φ), a₂ ≫ a = a₃ → b₂ ≫ b = b₃ →
        Function.Injective (cpull (mappingCone.map φ₂ φ a₃ b₃ comm₃) I (n + 1)) →
        ∀ (w : CohomologyClass K' I n) (c : CohomologyClass K I n), cpull a₂ I n w = cpull a₃ I n c → δ w = 0 := by
  set m := mappingCone.map φ' φ a b comm
  let e := AddEquiv.ofBijective _ hbij
  have he : ∀ y, cpull m I (n + 1) (e.symm y) = y := e.apply_symm_apply
  have he' : ∀ r, e.symm (cpull m I (n + 1) r) = r := e.symm_apply_apply
  have P1 := (coneSeq_exact R φ I (n + 1)).1
  have P3 := (coneSeq_exact R φ' I n).2.2
  have P3φ := (coneSeq_exact R φ I n).2.2
  refine ⟨(cpull (mappingCone.inr φ) I (n + 1)).comp
    (e.symm.toAddMonoidHom.comp (cpre (mappingCone.fst φ') I n (n + 1) (by omega))), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx1 : cpull φ I (n + 1) x = 0 := congrArg Prod.fst hx
      have hx2 : cpull b I (n + 1) x = 0 := congrArg Prod.snd hx
      obtain ⟨r, rfl⟩ := (P1 x).1 hx1
      have h0 : cpull (mappingCone.inr φ') I (n + 1) (cpull m I (n + 1) r) = 0 := by
        rw [cpull_inr_map]; exact hx2
      obtain ⟨w, hw⟩ := (P3 _).1 h0
      refine ⟨w, ?_⟩
      change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = _
      rw [hw, he']
    · rintro ⟨w, rfl⟩
      refine Prod.ext ((P1 _).2 ⟨_, rfl⟩) ?_
      change cpull b I (n + 1) (cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w))) = 0
      rw [← cpull_inr_map φ' φ a b comm, he]
      exact (P3 _).2 ⟨w, rfl⟩
  · intro K₂ L₂ φ₂ a₂ b₂ comm₂ a₃ b₃ comm₃ ha hb hinj w c hwc
    subst ha hb
    have hM : mappingCone.map φ₂ φ (a₂ ≫ a) (b₂ ≫ b) comm₃ =
        mappingCone.map φ₂ φ' a₂ b₂ comm₂ ≫ m := mappingCone.map_comp φ₂ φ' φ a₂ b₂ comm₂ a b comm
    have hr : e.symm (cpre (mappingCone.fst φ') I n (n + 1) (by omega) w) =
        cpre (mappingCone.fst φ) I n (n + 1) (by omega) c := by
      apply hinj
      rw [cpull_map_fst, ← hwc, hM, cpull_comp, he, cpull_map_fst]
    change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = 0
    rw [hr]
    exact (P3φ _).2 ⟨c, rfl⟩

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC


open NatRef in
theorem excision_boundary_natural_refine : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  intro q A A' _ _ _ f hN n i
  have hbij : ∀ (B : Type) [CommRing B] [Algebra A B], IsExcisionNbhd A B f →
      Function.Bijective (cpull (excisionConeMap (ZMod q) A B f) (res (ZMod q) (tw q i)) (n + 1)) := by
    intro B _ _ hB
    haveI := GlobalTheory.T.excisionConeMap_quasiIso' (ZMod q) A B f hB
    exact quasiIso_hypercohomology_bijective' (ZMod q) (excisionConeMap (ZMod q) A B f) (tw q i) (n + 1)
  obtain ⟨δ, hex, hnat⟩ := abstract_nat _ _ _ _ (excision_square_comm (ZMod q) A A' f) (res (ZMod q) (tw q i)) n
    (hbij A' hN)
  refine ⟨δ, hex, ?_⟩
  intro A₂ _ _ _ _ h₂ φ hφ w b hwb
  refine hnat ((chains (ZMod q)).map (spMap (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)))))
    ((chains (ZMod q)).map (spMap φ)) ((chains (ZMod q)).map (spMap (algebraMap A' A₂))) ?_ _ _
    (excision_square_comm (ZMod q) A A₂ f) ?_ ?_ (hbij A₂ h₂).1 w b hwb
  · rw [chains_spMap_comp, chains_spMap_comp, hφ]
  · rw [chains_spMap_comp]
    congr 2
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap, ← RingHom.comp_assoc, hφ,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · rw [chains_spMap_comp, ← IsScalarTower.algebraMap_eq]

end GlobalTheory.EtC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalExcisionBoundaryEtaleNbhdStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  first | (exact @GlobalTheory.EtC.excision_boundary_natural_refine) | (exact GlobalTheory.EtC.excision_boundary_natural_refine) | (intros; apply GlobalTheory.EtC.excision_boundary_natural_refine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem mvRefine (L1 : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0) (L2 : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a) : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  intro q A A' _ _ _ f hA' n i x hx1 hx2
  obtain ⟨δ, hδex, hδref⟩ := L1 q A A' f hA' n i
  obtain ⟨w, rfl⟩ := (hδex x).1 (by simp [hx1, hx2])
  refine ⟨w, ?_⟩
  intro g hfg A₂ C _ _ _ _ _ _ hA₂ hg hC a ha hcomp
  obtain ⟨b, hb⟩ := L2 q A C f g hfg hC n i a ha
  have hf2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hg2 : IsUnit (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)) (algebraMap A A₂ g)) := hg.map _
  let φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (algebraMap A A' f)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A' A₂))
      (by simpa [← IsScalarTower.algebraMap_apply] using hf2)
  let ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f) :=
    IsLocalization.Away.lift (f * g)
      (g := (algebraMap A₂ (Localization.Away (algebraMap A A₂ f))).comp (algebraMap A A₂))
      (by simpa using hf2.mul hg2)
  have hfg' : IsUnit (algebraMap A (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f * g)) (f * g))
  let ρ : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f (g := algebraMap A (Localization.Away (f * g))) hfg'
  have hφ : φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) := IsLocalization.Away.lift_comp _ _
  have hψ : ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) := IsLocalization.Away.lift_comp _ _
  have hρ : ρ.comp (algebraMap A _) = algebraMap A _ := IsLocalization.Away.lift_comp _ _
  have hψρ : ψ.comp ρ = Localization.awayMap (algebraMap A A₂) f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, hρ, hψ]
    exact (IsLocalization.map_comp _).symm
  refine hδref A₂ hA₂ φ hφ w b ?_
  rw [hcomp φ ψ hφ hψ, ← hb ρ hρ, ← pull_comp, ← spMap_comp_ring, hψρ]

theorem mvRefine_main : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := mvRefine GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd GlobalTheory.T.mayerVietoris_extend_class_coprime_etaleExcision

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinementStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleExcision_vanishing_under_refinement : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  first | (exact @GlobalTheory.EtC.mvRefine_main) | (exact GlobalTheory.EtC.mvRefine_main) | (intros; apply GlobalTheory.EtC.mvRefine_main <;> assumption)
end
end
