module

public import GroundTheory.GlobalFields.KummerTheory.Degree
public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Mathlib.FieldTheory.Galois.Abelian
public import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
public import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import GroundTheory.GlobalFields.ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm
public import GroundTheory.GlobalFields.FirstInequality
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
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.Tactic.TypeStar
public import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup
public import GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: GroundTheory.GlobalFields.PowerSubgroupIndex.Existence

section

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh IdeleGroup
  KummerIndex

universe u

section Power

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_map_powerSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K)).index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) :=
  firstInequality.index_map_powerSubgroup S hS hJ

end Power

section Prime

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

end Prime

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.ExistenceTheorem.KummerNorm

section

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  GroundTheory.ProfCoh SemiLocal

noncomputable section

universe u

theorem IdeleGroup.finiteProj_mem_units_of_ord_eq_zero {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} (h : ord v x = 0) :
    finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [ord_eq_zero_iff] at h
  refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
  · rw [coe_finiteProj]
    exact h.1
  · rw [← map_inv, coe_finiteProj]
    exact h.2

section SUnits

variable {K : Type u} [Field K] [NumberField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]


omit [HasEnoughRootsOfUnity K n] in
theorem unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K n).subgroupOf (S.unit K) = (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, mem_unitsPow, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    have hzu : z ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero z ^ n = 1 := by rw [← map_pow, hz, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨z, hzu⟩, Subtype.ext hz⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem index_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [unitsPow_subgroupOf_sUnit, SUnit.index_range_powMonoidHom]

instance finiteIndex_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).FiniteIndex :=
  ⟨by rw [index_unitsPow_subgroupOf_sUnit]; exact pow_ne_zero _ (NeZero.ne n)⟩


variable (K) in
abbrev sUnitKummerField (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  kummerExtension K n (AlgebraicClosure K) (S.unit K)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

instance sUnitKummerField.numberField : NumberField (sUnitKummerField K n S) :=
  NumberField.of_module_finite K _

instance sUnitKummerField.isAbelianGalois : IsAbelianGalois K (sUnitKummerField K n S) :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }

theorem finrank_sUnitKummerField :
    Module.finrank K (sUnitKummerField K n S) =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [finrank_kummerExtension, ← Subgroup.index, index_unitsPow_subgroupOf_sUnit]

end SUnits

section Symbol

attribute [local instance] galCommGroup

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S]

theorem ideleSymbol_adjoin_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {a : Kˣ} (ha : a ∈ S.unit K) (β : sUnitKummerField K n S)
    (hβ : β ^ n = algebraMap K _ (a : K)) {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (K⟮β⟯ : IntermediateField K (sUnitKummerField K n S)) x = 1 := by
  have hexpM : ∀ τ : Gal(sUnitKummerField K n S/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  have hexp : ∀ τ : Gal(K⟮β⟯/K), τ ^ n = 1 := by
    intro τ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K⟮β⟯)
      (E := sUnitKummerField K n S) τ
    rw [← map_pow, hexpM, map_one]
  have hβ' : (⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯) ^ n = algebraMap K K⟮β⟯ (a : K) :=
    Subtype.ext (by exact hβ)
  have hgen : adjoin K {(⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯)} = ⊤ :=
    lift_injective _ (by rw [lift_adjoin_simple, lift_top])
  have hinf : ∀ w, infiniteLocalSymbol K⟮β⟯ w (infiniteProj w x) = 1 := by
    intro w
    obtain ⟨t, ht⟩ := hx.2.1 w
    rw [← ht, powMonoidHom_apply, map_pow, hexp]
  have hfin : ∀ v, localSymbol K⟮β⟯ v (finiteProj v x) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨t, ht⟩ := hx.1 v hv
      rw [← ht, powMonoidHom_apply, map_pow, hexp]
    · have hord : ord v x = 0 := hx.2.2 v (by simpa using hv)
      obtain ⟨w⟩ := nonempty_placesOver K⟮β⟯ v
      have hnv : (n : 𝓞 K) ∉ v.asIdeal := fun h ↦ hv (hS v h)
      have hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)) := by
        have h := ha v hv
        rw [← valuationOfNeZero_eq] at h
        rw [← valuationOfNeZero_eq, show v.valuationOfNeZero a = 1 by exact_mod_cast h]
        simp
      have he := Kummer.ramificationIdx_eq_one_of_pow_eq (M := K⟮β⟯) a hβ' hgen v hnv hav
        w.1.asIdeal
      exact units_le_ker_localSymbol K⟮β⟯ v w he (finiteProj_mem_units_of_ord_eq_zero hord)
  rw [ideleSymbol_apply, finprod_eq_one_of_forall_eq_one hfin,
    Finset.prod_eq_one fun w _ ↦ hinf w, mul_one]

theorem ideleSymbol_sUnitKummerField_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (sUnitKummerField K n S) x = 1 := by
  set M := sUnitKummerField K n S
  have hfix : ∀ (β : M) (a : Kˣ), a ∈ S.unit K →
      (β : AlgebraicClosure K) ^ n = algebraMap K _ (a : K) → ideleSymbol K M x β = β := by
    intro β a ha hβ
    have hβ' : β ^ n = algebraMap K M (a : K) := Subtype.ext hβ
    have h1 := restrictNormal_ideleSymbol (K⟮β⟯ : IntermediateField K M) M x
    rw [ideleSymbol_adjoin_eq_one hS ha β hβ' hx, AlgEquiv.restrictNormal_eq_one_iff] at h1
    exact h1 β (mem_adjoin_simple_self K β)
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M)
    (s := {α : AlgebraicClosure K | ∃ a ∈ S.unit K, α ^ n = algebraMap K _ (a : K)}) rfl ?_
  rintro y ⟨a, ha, hy⟩
  exact hfix _ a ha hy

theorem map_powerSubgroup_le_range_ideleClassNorm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S ∅).map (IdeleClassGroup.mk K) ≤
      (ideleClassNorm K (sUnitKummerField K n S)).range := by
  rw [← ker_reciprocityMap, Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, reciprocityMap_mk]
  exact ideleSymbol_sUnitKummerField_eq_one hS hx

theorem range_ideleClassNorm_sUnitKummerField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range =
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) := by
  have hle := map_powerSubgroup_le_range_ideleClassNorm (n := n)
    (S := (S : Set (HeightOneSpectrum (𝓞 K)))) fun v hv ↦ Finset.mem_coe.2 (hS v hv)
  have h1 : (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range.index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_sUnitKummerField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]
  have h2 := index_map_powerSubgroup (n := n) S hS hJ
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, h2] at hrel
  have hone : ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map
      (IdeleClassGroup.mk K)).relIndex
      (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) (by rw [hrel, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hle

end Symbol

end

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.ExistenceTheorem.Kummer

section

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  GroundTheory.ProfCoh
open scoped NumberField.AdeleRing

noncomputable section

universe u

section Galois

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [Field M] [NumberField M] [Algebra K M]
  [IsAbelianGalois K M]

theorem reciprocityMap_intermediateField (L : IntermediateField K M) (c : IdeleClassGroup K) :
    reciprocityMap K L c = (reciprocityMap K M c).restrictNormal L := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, restrictNormal_ideleSymbol]

theorem range_ideleClassNorm_fixedField (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    (ideleClassNorm K (fixedField (N.map (reciprocityMap K M)))).range = N := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff]
  rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hk : d⁻¹ * c ∈ (reciprocityMap K M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
    rw [ker_reciprocityMap] at hk
    simpa using N.mul_mem hd (hN hk)
  · intro hc
    exact ⟨c, hc, rfl⟩

theorem exists_intermediateField_range_ideleClassNorm_eq_of_le (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    ∃ L : IntermediateField K M, (ideleClassNorm K L).range = N :=
  ⟨_, range_ideleClassNorm_fixedField N hN⟩

end Galois

section Open

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n]

theorem IdeleGroup.valued_finiteProj_eq_one_of_ord_eq_zero {v : HeightOneSpectrum (𝓞 K)}
    {x : IdeleGroup K} (h : ord v x = 0) :
    Valued.v ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  rw [coe_finiteProj, ← WithZero.exp_log (valued_ne_zero v x)]
  have h' : WithZero.log (Valued.v ((x : 𝔸[K]).2 v)) = 0 := by
    rw [ord] at h
    omega
  rw [h', WithZero.exp_zero]

theorem mem_congruenceSubgroup_of_eq_one (𝔪 : Modulus K) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v, 𝔪.exponent v ≠ 0 → v ∈ S) {z : IdeleGroup K} (hzS : ∀ v ∈ S, finiteProj v z = 1)
    (hzo : ∀ v ∉ S, ord v z = 0) (hzi : ∀ w, infiniteProj w z = 1) :
    z ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hv : v ∈ S
    · rw [hzS v hv]
      exact one_mem _
    · have he : 𝔪.exponent v = 0 := by
        by_contra h
        exact hv (hS v h)
      have h1 := valued_finiteProj_eq_one_of_ord_eq_zero (hzo v hv)
      rw [he, mem_unitsLevel]
      refine ⟨h1, ?_⟩
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ h1.le (by simp)
  · rw [hzi w.1]
    simp

theorem exists_map_powerSubgroup_le (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) ≤ N := by
  classical
  obtain ⟨𝔪, -, h𝔪⟩ := Modulus.exists_congruenceSubgroup_le (N.comap (IdeleClassGroup.mk K))
    (hN.preimage (IdeleClassGroup.continuous_mk K))
  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne n
  set P := (Ideal.finite_factors hn0).toFinset
  set T := 𝔪.finite_support_exponent.toFinset
  set S := S₀ ∪ T ∪ P with hSdef
  have hsub : (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊆ S := by
    intro v hv
    simp [hSdef, Finset.mem_coe.1 hv]
  refine ⟨S, fun v hv ↦ ?_, sup_sIdeles_eq_top_of_subset hsub hS₀, ?_⟩
  · have : v ∈ P := by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.2 hv
    simp [hSdef, this]
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  choose α hα using fun v : S ↦ hx.1 v.1 (Finset.mem_coe.2 v.2)
  choose β hβ using fun w ↦ hx.2.1 w
  let y : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hyS : ∀ v : S, finiteProj v.1 y = α v := by
    intro v
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hyo : ∀ v ∉ S, finiteProj v y = 1 := by
    intro v hv
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    exact Finset.prod_eq_one fun u _ ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hv (by rw [h]; exact u.2)) _
  have hyi : ∀ w, infiniteProj w y = β w := by
    intro w
    simp only [y, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  set z := (y ^ n)⁻¹ * x with hz
  have hzS : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 K))), finiteProj v z = 1 := by
    intro v hv
    rw [hz, map_mul, map_inv, map_pow, hyS ⟨v, hv⟩, ← hα ⟨v, hv⟩, powMonoidHom_apply,
      inv_mul_cancel]
  have hzo : ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ord v z = 0 := by
    intro v hv
    have hyv : ord v y = 0 := by
      rw [ord, ← coe_finiteProj, hyo v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]
    have hxv : ord v x = 0 := hx.2.2 v (by simpa using hv)
    rw [hz, ord_mul, ord_inv]
    have hpow' : ∀ k : ℕ, ord v (y ^ k) = 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ord_mul, ih, hyv, add_zero]
    rw [hpow' n, hxv]
    simp
  have hzi : ∀ w, infiniteProj w z = 1 := by
    intro w
    rw [hz, map_mul, map_inv, map_pow, hyi w, ← hβ w, powMonoidHom_apply, inv_mul_cancel]
  have hzU : z ∈ 𝔪.congruenceSubgroup :=
    mem_congruenceSubgroup_of_eq_one 𝔪 (S := (S : Set (HeightOneSpectrum (𝓞 K))))
      (fun v hv ↦ by
        have : v ∈ T := by
          rw [Set.Finite.mem_toFinset]
          exact hv
        simp [hSdef, this]) hzS hzo hzi
  have hxyz : x = y ^ n * z := by rw [hz, mul_inv_cancel_left]
  rw [hxyz]
  refine Subgroup.mul_mem _ ?_ (h𝔪 hzU)
  rw [Subgroup.mem_comap, map_pow]
  exact hpow _

end Open

section Existence

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem exists_intermediateField_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      ∃ L : IntermediateField K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))),
        (ideleClassNorm K L).range = N := by
  obtain ⟨S, hS, hJ, hle⟩ := exists_map_powerSubgroup_le N hN hpow
  refine ⟨S, hS, hJ, exists_intermediateField_range_ideleClassNorm_eq_of_le N ?_⟩
  rw [range_ideleClassNorm_sUnitKummerField S hS hJ]
  exact hle

theorem exists_isAbelianGalois_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ Monoid.exponent Gal(L/K) ∣ n ∧ (ideleClassNorm K L).range = N := by
  obtain ⟨S, -, -, L, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq N hN hpow
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hL⟩
  have hexpM : ∀ τ : Gal(sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun τ ↦ ?_
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L)
    (E := sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))) τ
  rw [← map_pow, hexpM, map_one]

end Existence

end

end GroundTheory.Global
end
end
