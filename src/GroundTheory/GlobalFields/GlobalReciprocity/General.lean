module

public import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
public import GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
import GroundTheory.GlobalFields.Adele.IdeleBasis
public import GroundTheory.GlobalFields.GlobalReciprocity.FinitePlaces
public import GroundTheory.GlobalFields.GlobalReciprocity.RealPlaces
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
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
import Mathlib.Tactic.TypeStar
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
import GroundTheory.GlobalFields.NormResidueSymbol.Surjective

-- Source module: GroundTheory.GlobalFields.GlobalReciprocity.RangeDiagonalLeKerIdeleSymbol

section

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup Filter Topology

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem range_ideleNorm_mem_nhds_one :
    ((ideleNorm K L).range : Set (IdeleGroup K)) ∈ 𝓝 1 := by
  classical
  let V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((finiteLocalNorm L v).range : Set (v.adicCompletion K)ˣ) ∩
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)
  have hV : ∀ᶠ v in cofinite, V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) := by
    filter_upwards [eventually_map_integerUnitsOver_eq (K := K) L] with v hv
    refine Set.inter_eq_right.2 ?_
    intro u hu
    have hu' : u ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
      rw [hv]
      exact hu
    obtain ⟨y, -, rfl⟩ := hu'
    exact ⟨y, rfl⟩
  have hopen := (IdeleGroup.isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((infiniteLocalNorm L w).range : Set (w.Completion)ˣ), V,
      fun w ↦ isOpen_range_infiniteLocalNorm w,
      fun v ↦ (isOpen_range_finiteLocalNorm v).inter (isOpen_units_adicCompletionIntegers K v),
      hV, rfl⟩
  refine mem_of_superset (hopen.mem_nhds ⟨fun w ↦ ?_, fun v ↦ ⟨?_, ?_⟩⟩) ?_
  · rw [map_one]
    exact one_mem _
  · rw [map_one]
    exact one_mem (finiteLocalNorm L v).range
  · rw [map_one]
    exact one_mem (Submonoid.ofClass (v.adicCompletionIntegers K)).units
  · rintro x ⟨hinf, hfin⟩
    exact mem_range_ideleNorm_of_forall x (fun v ↦ (hfin v).1) hinf

end IdeleNorm

theorem Abelianization.of_injective_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] :
    Function.Injective (Group.Abelianization.of : G →* Group.Abelianization G) := by
  rw [← MonoidHom.ker_eq_bot_iff, Group.Abelianization.ker_of, commutator_eq_bot]

namespace IdeleClassLimit

open FiniteSubfield

section Main

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem abstractSymbol_mk (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) =
      Group.Abelianization.of (ideleSymbol K.1 L.1 x) := by
  set f : IdeleGroup K.1 →* Group.Abelianization (L.1 ≃ₐ[K.1] L.1) :=
    (abstractSymbol K L).comp (IdeleClassGroup.mk K.1) with hf
  set g : IdeleGroup K.1 →* Group.Abelianization (L.1 ≃ₐ[K.1] L.1) :=
    Group.Abelianization.of.comp (ideleSymbol K.1 L.1) with hg
  have hle : localEmbeddingSubgroup K.1 ≤ f.eqLocus g :=
    sup_le (iSup_le fun v ↦ by
        rintro _ ⟨a, rfl⟩
        change abstractSymbol K L (IdeleClassGroup.mk K.1 (finiteEmbedding v a)) =
          Group.Abelianization.of (ideleSymbol K.1 L.1 (finiteEmbedding v a))
        rw [abstractSymbol_mk_finiteEmbedding, ideleSymbol_finiteEmbedding])
      (iSup_le fun w ↦ by
        rintro _ ⟨a, rfl⟩
        change abstractSymbol K L (IdeleClassGroup.mk K.1 (infiniteEmbedding w a)) =
          Group.Abelianization.of (ideleSymbol K.1 L.1 (infiniteEmbedding w a))
        rw [abstractSymbol_mk_infiniteEmbedding, ideleSymbol_infiniteEmbedding])
  have hfN : ∀ y : IdeleGroup L.1, f (ideleNorm K.1 L.1 y) = 1 := fun y ↦
    abstractSymbol_ideleClassNorm_eq_one K L (IdeleClassGroup.mk L.1 y)
  have hgN : ∀ y : IdeleGroup L.1, g (ideleNorm K.1 L.1 y) = 1 := fun y ↦ by
    change Group.Abelianization.of (ideleSymbol K.1 L.1 (ideleNorm K.1 L.1 y)) = 1
    rw [ideleSymbol_ideleNorm, map_one]
  obtain ⟨h, hh, ⟨y, hy⟩⟩ :=
    exists_mem_localEmbeddingSubgroup_inv_mul_mem (IdeleNorm.range_ideleNorm_mem_nhds_one L.1) x
  have hx : x = h * ideleNorm K.1 L.1 y := by rw [hy, mul_inv_cancel_left]
  change f x = g x
  rw [hx, map_mul, map_mul, hfN, hgN, (hle hh : f h = g h)]

theorem ideleSymbol_diagonal (a : K.1ˣ) : ideleSymbol K.1 L.1 (diagonal K.1 a) = 1 := by
  apply Abelianization.of_injective_of_isMulCommutative
  rw [← abstractSymbol_mk, IdeleClassGroup.mk_diagonal, map_one, map_one]

theorem range_diagonal_le_ker_ideleSymbol :
    (diagonal K.1).range ≤ (ideleSymbol K.1 L.1).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal K L a

abbrev classSymbol : IdeleClassGroup K.1 →* (L.1 ≃ₐ[K.1] L.1) :=
  CyclotomicSymbol.ideleClassSymbol L.1 (range_diagonal_le_ker_ideleSymbol K L)

theorem abstractSymbol_eq_classSymbol :
    abstractSymbol K L = Group.Abelianization.of.comp (classSymbol K L) := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
  exact abstractSymbol_mk K L x

theorem ker_abstractSymbol :
    (abstractSymbol K L).ker = (FiniteSubfield.ideleClassNorm hKL.out).range := by
  ext c
  rw [MonoidHom.mem_ker, abstractSymbol_apply]
  have hinj : Function.Injective (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom) :=
    fun a b hab ↦ (quotientGaloisEquiv K L).abelianizationCongr.injective hab
  rw [← map_one (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom), hinj.eq_iff,
    ← map_one (reciprocityEquiv K L).symm, (reciprocityEquiv K L).symm.injective.eq_iff]
  constructor
  · intro h
    change (QuotientGroup.mk (fixedEquiv K c) : GroundTheory.LocalField.Abstract.tateZero IdeleClassLimit
      (K.openSubgroup : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) L.openSubgroup) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨d, rfl⟩ := (fixedEquiv L).surjective b
    refine ⟨d, (fixedEquiv K).injective ?_⟩
    rw [← norm_fixedEquiv hKL.out d]
    exact hb
  · rintro ⟨d, rfl⟩
    exact normClass_ideleClassNorm K L d

theorem ker_classSymbol :
    (classSymbol K L).ker = (FiniteSubfield.ideleClassNorm hKL.out).range := by
  ext c
  rw [← ker_abstractSymbol K L, MonoidHom.mem_ker, MonoidHom.mem_ker, abstractSymbol_eq_classSymbol K L,
    MonoidHom.comp_apply, ← map_one Group.Abelianization.of,
    Abelianization.of_injective_of_isMulCommutative.eq_iff]

theorem ker_ideleSymbol :
    (ideleSymbol K.1 L.1).ker = (diagonal K.1).range ⊔ (ideleNorm K.1 L.1).range := by
  refine le_antisymm (fun x hx ↦ ?_)
    (sup_le (range_diagonal_le_ker_ideleSymbol K L) (range_ideleNorm_le_ker_ideleSymbol L.1))
  have hc : IdeleClassGroup.mk K.1 x ∈ (classSymbol K L).ker := hx
  rw [ker_classSymbol] at hc
  obtain ⟨c, hc⟩ := hc
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L.1 c
  have hy : IdeleClassGroup.mk K.1 (ideleNorm K.1 L.1 y) = IdeleClassGroup.mk K.1 x := hc
  have hd : (ideleNorm K.1 L.1 y)⁻¹ * x ∈ (diagonal K.1).range := by
    rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hx : x = ideleNorm K.1 L.1 y * ((ideleNorm K.1 L.1 y)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨y, rfl⟩) (Subgroup.mem_sup_left hd)

end Main

end IdeleClassLimit

end

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.GlobalReciprocity.General

section

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace FiniteSubfield

variable {F E : FiniteSubfield} [Fact (F ≤ E)]

theorem apply_mem_of_normal_field [Normal F.1 E.1] {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ F.1.fixingSubgroup)
    {x : ℚ̄} (hx : x ∈ E.1) : g x ∈ E.1 := by
  let g' : ℚ̄ ≃ₐ[F.1] ℚ̄ := IntermediateField.fixingSubgroupEquiv F.1 ⟨g, hg⟩
  have : IsScalarTower F.1 E.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h := AlgEquiv.restrictNormal_commutes g' E.1 ⟨x, hx⟩
  have e : g' x = g x := rfl
  rw [← e, ← show algebraMap E.1 ℚ̄ ⟨x, hx⟩ = x from rfl, ← h]
  exact (g'.restrictNormal E.1 ⟨x, hx⟩).2

theorem normal_subgroupOf_of_isGalois [IsGalois F.1 E.1] :
    (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal := by
  refine ⟨fun l hl g ↦ ?_⟩
  rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hl ⊢
  intro x hx
  have hy : ((g⁻¹ : F.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x ∈ E.1 :=
    apply_mem_of_normal_field (g⁻¹ : F.1.fixingSubgroup).2 hx
  change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((l : ℚ̄ ≃ₐ[ℚ] ℚ̄) (((g⁻¹ : F.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x)) = x
  rw [hl _ hy, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

end FiniteSubfield

section Transfer

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


omit [NumberField K] [NumberField K'] in
theorem finrank_eq_one_of_bijective (hK : Function.Bijective (algebraMap K K')) :
    Module.finrank K K' = 1 :=
  (AlgEquiv.ofBijective (Algebra.ofId K K') hK).toLinearEquiv.finrank_eq.symm.trans
    (Module.finrank_self K)


omit [Algebra K L] [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L']
  [IsScalarTower K L L'] in
theorem ideleNorm_ideleEmbedding_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (x : IdeleGroup K) : ideleNorm K K' (ideleEmbedding K K' x) = x := by
  rw [ideleNorm_ideleEmbedding, finrank_eq_one_of_bijective hK, pow_one]

variable [IsGalois K L]


omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in
theorem restrictNormal_restrictScalars_eq_one (hL : Function.Bijective (algebraMap L L'))
    {σ : L' ≃ₐ[K'] L'} (h : (σ.restrictScalars K).restrictNormal L = 1) : σ = 1 := by
  refine AlgEquiv.ext fun y ↦ ?_
  obtain ⟨l, rfl⟩ := hL.2 y
  have e := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L l
  rw [h, AlgEquiv.one_apply] at e
  exact e.symm

variable [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem ideleSymbol_diagonal_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (hA : ∀ a : K'ˣ, ideleSymbol K' L' (diagonal K' a) = 1) (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 := by
  rw [← ideleNorm_ideleEmbedding_of_bijective hK (diagonal K a),
    ← restrictNormal_restrictScalars_ideleSymbol (L := L) (L' := L'), ideleEmbedding_diagonal, hA]
  exact map_one ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp (restrictScalarsHom K))

theorem ker_ideleSymbol_le_of_bijective (hK : Function.Bijective (algebraMap K K'))
    (hL : Function.Bijective (algebraMap L L'))
    (hker : (ideleSymbol K' L').ker ≤ (diagonal K').range ⊔ (ideleNorm K' L').range) :
    (ideleSymbol K L).ker ≤ (diagonal K).range ⊔ (ideleNorm K L).range := by
  intro x hx
  have h1 : ideleSymbol K' L' (ideleEmbedding K K' x) = 1 := by
    refine restrictNormal_restrictScalars_eq_one (K := K) hL ?_
    rw [restrictNormal_restrictScalars_ideleSymbol, ideleNorm_ideleEmbedding_of_bijective hK]
    exact hx
  have hmap : ((diagonal K').range ⊔ (ideleNorm K' L').range).map (ideleNorm K K') ≤
      (diagonal K).range ⊔ (ideleNorm K L).range := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨_, (ideleNorm_diagonal b).symm⟩
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨ideleNorm L L' y, by rw [ideleNorm_ideleNorm, ideleNorm_ideleNorm]⟩
  rw [← ideleNorm_ideleEmbedding_of_bijective hK x]
  exact hmap ⟨_, hker h1, rfl⟩

end Transfer

section Embedding

def rangeMap {A : Type*} [Field A] [Algebra ℚ A] (f : A →ₐ[ℚ] ℚ̄) : A →+* f.fieldRange where
  toFun a := ⟨f a, a, rfl⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a b)
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)

theorem rangeMap_bijective {A : Type*} [Field A] [Algebra ℚ A] (f : A →ₐ[ℚ] ℚ̄) :
    Function.Bijective (rangeMap f) :=
  ⟨(rangeMap f).injective, by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩⟩

theorem finiteDimensional_fieldRange {A : Type*} [Field A] [NumberField A] (f : A →ₐ[ℚ] ℚ̄) :
    FiniteDimensional ℚ f.fieldRange :=
  Module.Finite.of_surjective
    ({ toFun := rangeMap f, map_add' := map_add _, map_smul' := fun c a ↦ Subtype.ext (f.toLinearMap.map_smul c a) } :
      A →ₗ[ℚ] f.fieldRange) (rangeMap_bijective f).2

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def embedding : L →ₐ[ℚ] ℚ̄ := IsAlgClosed.lift

def baseEmbedding : K →ₐ[ℚ] ℚ̄ := (embedding L).comp (IsScalarTower.toAlgHom ℚ K L)

def topField : FiniteSubfield := ⟨(embedding L).fieldRange, finiteDimensional_fieldRange _⟩

def baseField : FiniteSubfield := ⟨(baseEmbedding K L).fieldRange, finiteDimensional_fieldRange _⟩

instance fact_baseField_le : Fact (baseField K L ≤ topField L) :=
  ⟨by
    rintro _ ⟨k, rfl⟩
    exact ⟨algebraMap K L k, rfl⟩⟩

variable {K L} [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal_and_ker_le :
    (∀ a : Kˣ, ideleSymbol K L (diagonal K a) = 1) ∧
      (ideleSymbol K L).ker ≤ (diagonal K).range ⊔ (ideleNorm K L).range := by
  let K' := baseField K L
  let L' := topField L
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K L)).toAlgebra
  let _ : Algebra L L'.1 := (rangeMap (embedding L)).toAlgebra
  let _ : Algebra K L'.1 := ((rangeMap (embedding L)).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K K'.1 L'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K L L'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hL : Function.Bijective (algebraMap L L'.1) := rangeMap_bijective _
  have : IsGalois K L'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L L'.1) hL)
  have : IsGalois K'.1 L'.1 := IsGalois.tower_top_of_isGalois K K'.1 L'.1
  have : IsMulCommutative (L'.1 ≃ₐ[K'.1] L'.1) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    let f := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L'.1) L).comp (restrictScalarsHom (K' := K'.1) (L' := L'.1) K)
    have h := restrictNormal_restrictScalars_eq_one (K := K) (K' := K'.1) (L := L) (L' := L'.1) hL
      (σ := σ * τ * (τ * σ)⁻¹) (by
      change f (σ * τ * (τ * σ)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm' (f σ) (f τ), mul_inv_cancel])
    rwa [mul_inv_eq_one] at h
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := L')
  exact ⟨ideleSymbol_diagonal_of_bijective hK (IdeleClassLimit.ideleSymbol_diagonal K' L'),
    ker_ideleSymbol_le_of_bijective hK hL (IdeleClassLimit.ker_ideleSymbol K' L').le⟩

end Embedding

section Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal (a : Kˣ) : ideleSymbol K L (diagonal K a) = 1 :=
  ideleSymbol_diagonal_and_ker_le.1 a

theorem diagonal_range_le_ker_ideleSymbol : (diagonal K).range ≤ (ideleSymbol K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal a

theorem ker_ideleSymbol : (ideleSymbol K L).ker = (diagonal K).range ⊔ (ideleNorm K L).range :=
  le_antisymm ideleSymbol_diagonal_and_ker_le.2
    (sup_le diagonal_range_le_ker_ideleSymbol (range_ideleNorm_le_ker_ideleSymbol L))


omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
instance ideleClassNorm_range_normal : (ideleClassNorm K L).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩


variable (K L) in
def reciprocityMap : IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) diagonal_range_le_ker_ideleSymbol

@[simp]
theorem reciprocityMap_mk (x : IdeleGroup K) :
    reciprocityMap K L (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_reciprocityMap : Continuous (reciprocityMap K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

theorem ker_reciprocityMap : (reciprocityMap K L).ker = (ideleClassNorm K L).range := by
  ext c
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [MonoidHom.mem_ker, reciprocityMap_mk, ← MonoidHom.mem_ker, ker_ideleSymbol]
  constructor
  · intro hx
    obtain ⟨d, hd, n, hn, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨y, rfl⟩ := hn
    obtain ⟨a, rfl⟩ := hd
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K (ideleNorm K L y))).symm
  · rintro ⟨c', hc'⟩
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c'
    rw [ideleClassNorm_mk] at hc'
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hc', inv_mul_cancel]
    rw [← mul_inv_cancel_left (ideleNorm K L y) x]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨y, rfl⟩) (Subgroup.mem_sup_left hd)

end Reciprocity

universe u

section Isomorphism

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem reciprocityMap_surjective : Function.Surjective (reciprocityMap K L) := fun σ ↦
  let ⟨x, hx⟩ := ideleSymbol_surjective (K := K) (L := L) σ
  ⟨IdeleClassGroup.mk K x, hx⟩


variable (K L) in
def reciprocityMapEquiv : IdeleClassGroup K ⧸ (ideleClassNorm K L).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_reciprocityMap (K := K) (L := L)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ reciprocityMap_surjective)

theorem index_range_ideleClassNorm_eq_finrank_of_isMulCommutative : (ideleClassNorm K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (reciprocityMapEquiv K L).toEquiv, IsGalois.card_aut_eq_finrank]

end Isomorphism

end

end GroundTheory.Global
end
end
