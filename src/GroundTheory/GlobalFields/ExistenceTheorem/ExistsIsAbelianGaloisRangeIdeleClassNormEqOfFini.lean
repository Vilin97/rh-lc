module

public import GroundTheory.GlobalFields.GlobalReciprocity.General
public import Mathlib.FieldTheory.Galois.Abelian
public import GroundTheory.GlobalFields.ExistenceTheorem.Kummer
public import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
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
import Mathlib.GroupTheory.Schreier
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.TypeStar
import GroundTheory.LocalFields.LubinTateUnramified

-- Source module: GroundTheory.GlobalFields.ExistenceTheorem.NormLimitation

section

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

noncomputable section

section MaxAbelian

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

def maxAbelian : IntermediateField K M := fixedField (commutator Gal(M/K))

variable [FiniteDimensional K M] [IsGalois K M]

instance isGalois_maxAbelian : IsGalois K (maxAbelian K M) :=
  IsGalois.of_fixedField_normal_subgroup _

instance isMulCommutative_maxAbelian : IsMulCommutative Gal(maxAbelian K M/K) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  let e : Gal(M/K) ⧸ commutator Gal(M/K) ≃* Gal(maxAbelian K M/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  obtain ⟨a, rfl⟩ := e.surjective σ
  obtain ⟨b, rfl⟩ := e.surjective τ
  rw [← map_mul, ← map_mul]
  exact congrArg e (mul_comm (G := Group.Abelianization Gal(M/K)) a b)

instance isAbelianGalois_maxAbelian : IsAbelianGalois K (maxAbelian K M) where

theorem finrank_maxAbelian :
    Module.finrank K (maxAbelian K M) = Nat.card (Group.Abelianization Gal(M/K)) := by
  have h1 := Module.finrank_mul_finrank K (maxAbelian K M) M
  rw [maxAbelian, finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M,
    ← (commutator Gal(M/K)).card_mul_index] at h1
  have hpos : 0 < Nat.card (commutator Gal(M/K)) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end MaxAbelian

namespace IdeleClassLimit

open FiniteSubfield GroundTheory.LocalField.Abstract

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem ker_abstractSymbol_le :
    (abstractSymbol K L).ker ≤ (FiniteSubfield.ideleClassNorm hKL.out).range := by
  intro c hc
  rw [MonoidHom.mem_ker, abstractSymbol_apply] at hc
  have hinj : Function.Injective (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom) :=
    fun a b hab ↦ (quotientGaloisEquiv K L).abelianizationCongr.injective hab
  rw [← map_one (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom), hinj.eq_iff,
    ← map_one (reciprocityEquiv K L).symm, (reciprocityEquiv K L).symm.injective.eq_iff] at hc
  change (QuotientGroup.mk (fixedEquiv K c) : tateZero IdeleClassLimit
    (K.openSubgroup : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) L.openSubgroup) = 1 at hc
  rw [QuotientGroup.eq_one_iff] at hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨d, rfl⟩ := (fixedEquiv L).surjective b
  refine ⟨d, (fixedEquiv K).injective ?_⟩
  rw [← norm_fixedEquiv hKL.out d]
  exact hb

theorem index_range_ideleClassNorm_dvd :
    (FiniteSubfield.ideleClassNorm hKL.out).range.index ∣
      Nat.card (Group.Abelianization (L.1 ≃ₐ[K.1] L.1)) := by
  refine (Subgroup.index_dvd_of_le (ker_abstractSymbol_le K L)).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card (abstractSymbol K L).range

end IdeleClassLimit

section Transport

theorem index_range_ideleClassNorm_dvd_card_abelianization {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] :
    (ideleClassNorm K M).range.index ∣ Nat.card (Group.Abelianization Gal(M/K)) := by
  let K' := baseField K M
  let M' := topField M
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K M)).toAlgebra
  let _ : Algebra M M'.1 := (rangeMap (embedding M)).toAlgebra
  let _ : Algebra K M'.1 := ((rangeMap (embedding M)).comp (algebraMap K M)).toAlgebra
  have : IsScalarTower K K'.1 M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K M M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hM : Function.Bijective (algebraMap M M'.1) := rangeMap_bijective _
  have : IsGalois K M'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K M M'.1) hM)
  have : IsGalois K'.1 M'.1 := IsGalois.tower_top_of_isGalois K K'.1 M'.1
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := M')
  have h1 := IdeleClassLimit.index_range_ideleClassNorm_dvd K' M'
  have hrange : (ideleClassNorm K M).range =
      (ideleClassNorm K'.1 M'.1).range.map (ideleClassNorm K K'.1) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨ideleClassNorm K'.1 M'.1 (ideleClassMap M M'.1 d), ⟨_, rfl⟩, ?_⟩
      rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := M),
        ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hM, pow_one]
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      exact ⟨ideleClassNorm M M'.1 d, by
        rw [ideleClassNorm_ideleClassNorm, ideleClassNorm_ideleClassNorm]⟩
  have hsurj : Function.Surjective (ideleClassNorm K K'.1) := fun c ↦
    ⟨ideleClassMap K K'.1 c, by
      rw [ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hK, pow_one]⟩
  have hcard : Nat.card (Group.Abelianization Gal(M'.1/K'.1)) =
      Nat.card (Group.Abelianization Gal(M/K)) := by
    let f : Gal(M'.1/K'.1) →* Gal(M/K) :=
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M'.1) M).comp (restrictScalarsHom K)
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      exact restrictNormal_restrictScalars_eq_one (K := K) hM hσ
    have hc : Nat.card Gal(M'.1/K'.1) = Nat.card Gal(M/K) := by
      rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      have e1 := Module.finrank_mul_finrank K K'.1 M'.1
      have e2 := Module.finrank_mul_finrank K M M'.1
      rw [finrank_eq_one_of_bijective hK, one_mul] at e1
      rw [finrank_eq_one_of_bijective hM, mul_one] at e2
      rw [e1, e2]
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hc.ge
    exact Nat.card_congr (MulEquiv.ofBijective f hbij).abelianizationCongr.toEquiv
  rw [hrange, ← hcard]
  exact (Subgroup.index_map_dvd _ hsurj).trans h1

universe u

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

theorem range_ideleClassNorm_maxAbelian :
    (ideleClassNorm K (maxAbelian K M)).range = (ideleClassNorm K M).range := by
  have hle : (ideleClassNorm K M).range ≤ (ideleClassNorm K (maxAbelian K M)).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm (maxAbelian K M) M c, ideleClassNorm_ideleClassNorm c⟩
  have hE : (ideleClassNorm K (maxAbelian K M)).range.index =
      Nat.card (Group.Abelianization Gal(M/K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_maxAbelian]
  have hne : (ideleClassNorm K (maxAbelian K M)).range.index ≠ 0 := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'
  have heq : (ideleClassNorm K M).range.index = (ideleClassNorm K (maxAbelian K M)).range.index :=
    Nat.dvd_antisymm (hE ▸ index_range_ideleClassNorm_dvd_card_abelianization)
      (Subgroup.index_dvd_of_le hle)
  have hrel := Subgroup.relIndex_mul_index hle
  rw [heq] at hrel
  have h1 : (ideleClassNorm K M).range.relIndex (ideleClassNorm K (maxAbelian K M)).range = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hrel.trans (one_mul _).symm)
    exact this
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle


omit [IsGalois K M] in
theorem exists_isAbelianGalois_range_ideleClassNorm_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range ≤ (ideleClassNorm K L).range := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K L Ω
  have : IsAlgClosure K Ω := ⟨AlgebraicClosure.isAlgClosed L, inferInstance⟩
  let N := normalClosure K L Ω
  have : IsGalois K N := ⟨⟩
  have : NumberField N := NumberField.of_module_finite K N
  refine ⟨maxAbelian K N, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [range_ideleClassNorm_maxAbelian]
  rintro _ ⟨c, rfl⟩
  exact ⟨ideleClassNorm L N c, ideleClassNorm_ideleClassNorm c⟩

end Transport

end

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini

section

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup

noncomputable section

universe u

instance numberField_of_finiteDimensional {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L] : NumberField L :=
  NumberField.of_module_finite K L

section NormGroup

variable {K : Type*} [Field K] [NumberField K]

theorem range_ideleClassNorm_congr {L L' : Type*} [Field L] [NumberField L] [Field L']
    [NumberField L'] [Algebra K L] [Algebra K L'] (τ : L ≃ₐ[K] L') :
    (ideleClassNorm K L').range = (ideleClassNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨e, rfl⟩ := (ideleClassEquiv (τ : L ≃+* L')).surjective d
    exact ⟨e, (ideleClassNorm_ideleClassEquiv τ e).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, ideleClassNorm_ideleClassEquiv τ d⟩

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]

theorem range_ideleClassNorm_eq_comap (F : IntermediateField K M) :
    (ideleClassNorm K F).range = F.fixingSubgroup.comap (reciprocityMap K M) := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]

end NormGroup

section Compositum

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem isMulCommutative_sup (L₁ L₂ : IntermediateField K Ω) [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂] [Normal K ↥(L₁ ⊔ L₂)] : IsMulCommutative Gal(↥(L₁ ⊔ L₂)/K) := by
  have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
  have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
  have key : ∀ (L : IntermediateField K Ω) [IsAbelianGalois K L] (h : L ≤ L₁ ⊔ L₂)
      (σ τ : Gal(↥(L₁ ⊔ L₂)/K)), (τ * σ)⁻¹ * (σ * τ) ∈ (restrict h).fixingSubgroup := by
    intro L _ h σ τ
    let _ : Algebra L ↥(L₁ ⊔ L₂) := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L ↥(L₁ ⊔ L₂) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨x, rfl⟩ : ∃ x : L, algebraMap L ↥(L₁ ⊔ L₂) x = y := ⟨⟨y, (mem_restrict h y).1 hy⟩, rfl⟩
    have hm : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm' (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L τ), inv_mul_cancel]
    have hc := AlgEquiv.restrictNormal_commutes ((τ * σ)⁻¹ * (σ * τ)) L x
    change algebraMap L _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L
      ((τ * σ)⁻¹ * (σ * τ)) x) = _ at hc
    rw [hm, AlgEquiv.one_apply] at hc
    exact hc.symm
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  have htop : restrict h₁ ⊔ restrict h₂ = (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)) := by
    refine top_unique fun y _ ↦ ?_
    have hy : (y : Ω) ∈ lift (restrict h₁) ⊔ lift (restrict h₂) := by
      rw [lift_restrict, lift_restrict]
      exact y.2
    rw [← lift_sup] at hy
    exact (mem_lift y).1 hy
  have hρ : (τ * σ)⁻¹ * (σ * τ) ∈ (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)).fixingSubgroup := by
    rw [← htop, fixingSubgroup_sup]
    exact ⟨key L₁ h₁ σ τ, key L₂ h₂ σ τ⟩
  have h1 : (τ * σ)⁻¹ * (σ * τ) = 1 :=
    AlgEquiv.ext fun y ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ y mem_top
  rw [inv_mul_eq_one] at h1
  exact h1.symm

instance isAbelianGalois_sup [CharZero K] (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    IsAbelianGalois K ↥(L₁ ⊔ L₂) :=
  have : IsGalois K ↥(L₁ ⊔ L₂) := ⟨⟩
  { toIsMulCommutative := isMulCommutative_sup L₁ L₂ }

end Compositum

section Existence

variable {K : Type u} [Field K] [NumberField K]

theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] (N : Subgroup (IdeleClassGroup K)) (hN : (ideleClassNorm K L).range ≤ N) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range = N := by
  obtain ⟨E, _, _, _, _, hE⟩ := exists_isAbelianGalois_range_ideleClassNorm_le (K := K) L
  exact ⟨fixedField (N.map (reciprocityMap K E)), inferInstance, inferInstance, inferInstance,
    inferInstance, range_ideleClassNorm_fixedField N (hE.trans hN)⟩

theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ (ideleClassNorm K L).range = N := by
  have : NeZero N.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  let K' := CyclotomicField N.index K
  have : HasEnoughRootsOfUnity K' N.index :=
    ⟨⟨_, IsCyclotomicExtension.zeta_spec N.index K K'⟩, rootsOfUnity.isCyclic _ _⟩
  let N' := N.comap (ideleClassNorm K K')
  have hN' : IsOpen (N' : Set (IdeleClassGroup K')) := hN.preimage continuous_ideleClassNorm
  have : N.Normal := ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  have hpow : ∀ c, c ^ N.index ∈ N' := fun c ↦ by
    rw [Subgroup.mem_comap, map_pow]
    exact N.pow_index_mem _
  obtain ⟨L', _, _, _, -, -, hL'⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq N' hN' hpow
  let _ : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine exists_isAbelianGalois_range_ideleClassNorm_eq_of_le L' N ?_
  rintro _ ⟨c, rfl⟩
  rw [← ideleClassNorm_ideleClassNorm (L := K')]
  have hc : ideleClassNorm K' L' c ∈ N' := hL' ▸ ⟨c, rfl⟩
  exact hc

end Existence

section Open

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

theorem isOpen_range_ideleClassNorm :
    IsOpen ((ideleClassNorm K L).range : Set (IdeleClassGroup K)) := by
  rw [← ker_reciprocityMap, MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage continuous_reciprocityMap

instance finiteIndex_range_ideleClassNorm : (ideleClassNorm K L).range.FiniteIndex :=
  ⟨by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'⟩

end Open

section Correspondence

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]

theorem range_ideleClassNorm_le_range_iff (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    (ideleClassNorm K L₂).range ≤ (ideleClassNorm K L₁).range ↔ L₁ ≤ L₂ := by
  constructor
  · intro h
    have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
    have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
    have e₁ : (ideleClassNorm K (restrict h₁)).range = (ideleClassNorm K L₁).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₁))
    have e₂ : (ideleClassNorm K (restrict h₂)).range = (ideleClassNorm K L₂).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₂))
    rw [← e₁, ← e₂, range_ideleClassNorm_eq_comap, range_ideleClassNorm_eq_comap,
      Subgroup.comap_le_comap_of_surjective reciprocityMap_surjective] at h
    have hF : restrict h₁ ≤ restrict h₂ := by
      rw [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le]
      exact h
    intro x hx
    exact (mem_restrict h₂ ⟨x, h₁ hx⟩).1 (hF ((mem_restrict h₁ ⟨x, h₁ hx⟩).2 hx))
  · intro h
    let _ : Algebra L₁ L₂ := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm L₁ L₂ c, ideleClassNorm_ideleClassNorm c⟩

variable [IsAlgClosed Ω]

theorem exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (ideleClassNorm K L).range = N := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex N hN
  let f : L →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := LinearEquiv.finiteDimensional τ.toLinearEquiv
  have : IsAbelianGalois K f.fieldRange := IsAbelianGalois.of_algHom τ.symm.toAlgHom
  exact ⟨f.fieldRange, inferInstance, inferInstance, (range_ideleClassNorm_congr τ).trans hL⟩


variable (K Ω) in
abbrev FiniteAbelianSubfield : Type u :=
  {L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}


variable (K) in
abbrev OpenFiniteIndexSubgroup : Type u :=
  {N : Subgroup (IdeleClassGroup K) // IsOpen (N : Set (IdeleClassGroup K)) ∧ N.FiniteIndex}

def normGroup (L : FiniteAbelianSubfield K Ω) : OpenFiniteIndexSubgroup K :=
  haveI := L.2.1
  haveI := L.2.2
  ⟨(ideleClassNorm K L.1).range, isOpen_range_ideleClassNorm, inferInstance⟩

theorem normGroup_le_normGroup_iff (L₁ L₂ : FiniteAbelianSubfield K Ω) :
    normGroup L₂ ≤ normGroup L₁ ↔ L₁ ≤ L₂ := by
  have := L₁.2.1
  have := L₁.2.2
  have := L₂.2.1
  have := L₂.2.2
  exact range_ideleClassNorm_le_range_iff L₁.1 L₂.1

theorem normGroup_injective : Function.Injective (normGroup (K := K) (Ω := Ω)) := fun L₁ L₂ h ↦
  le_antisymm ((normGroup_le_normGroup_iff L₁ L₂).1 h.ge) ((normGroup_le_normGroup_iff L₂ L₁).1 h.le)

theorem normGroup_surjective : Function.Surjective (normGroup (K := K) (Ω := Ω)) := fun N ↦ by
  have := N.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω)
    N.1 N.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩


variable (K Ω) in
def normGroupOrderIso : FiniteAbelianSubfield K Ω ≃o (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective normGroup ⟨normGroup_injective, normGroup_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' {L₁ L₂} := normGroup_le_normGroup_iff L₁ L₂

theorem normGroupOrderIso_apply (L : FiniteAbelianSubfield K Ω) :
    OrderDual.ofDual (normGroupOrderIso K Ω L) = normGroup L :=
  rfl

end Correspondence

end

end GroundTheory.Global
end
end
