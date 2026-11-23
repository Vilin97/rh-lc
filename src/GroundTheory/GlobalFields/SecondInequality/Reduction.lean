module

public import GroundTheory.GlobalFields.SecondInequality.Statement
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
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
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

-- Source module: GroundTheory.GlobalFields.SecondInequality.PrimeDegree

section

@[expose] public section

namespace GroundTheory.Global

open NumberField Module Polynomial IntermediateField

universe u

section PrimeDegree

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem SecondInequalityRoots.index_le_of_prime (hR : SecondInequalityRoots.{u}) [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hL : finrank K L = p) :
    (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let E := CyclotomicField p L
  let ζ : E := IsCyclotomicExtension.zeta p L E
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p L E
  let K' : IntermediateField K E := K⟮ζ⟯

  have hroot : aeval ζ (cyclotomic p K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hp.pos
  have hd_lt : finrank K K' < p := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
    have h1 := minpoly.degree_le_of_ne_zero K ζ (cyclotomic_ne_zero p K) hroot
    have h2 : (minpoly K ζ).natDegree ≤ (cyclotomic p K).natDegree := natDegree_le_natDegree h1
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    have := hp.two_le
    omega
  have hd_pos : 0 < finrank K K' := finrank_pos
  have hcop : (finrank K K').Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)).symm

  let ζ' : K' := ⟨ζ, mem_adjoin_simple_self K ζ⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap K' E) (algebraMap K' E).injective).1 hζ
  have hroots : HasEnoughRootsOfUnity K' p := ⟨⟨ζ', hζ'⟩, rootsOfUnity.isCyclic K' p⟩

  obtain ⟨f, hfsep, hf⟩ := IsGalois.is_separable_splitting_field (F := K) (E := L)
  have := hf
  have : IsSplittingField L E ((cyclotomic p K).map (algebraMap K L)) := by
    rw [map_cyclotomic]
    exact IsCyclotomicExtension.splitting_field_cyclotomic p L E
  have : IsSplittingField K E (f * cyclotomic p K) :=
    IsSplittingField.mul (F := K) (K := L) (L := E) f (cyclotomic p K) hfsep.ne_zero (cyclotomic_ne_zero p K)
  have : IsGalois K E :=
    { to_isSeparable := inferInstance, to_normal := Normal.of_isSplittingField (f * cyclotomic p K) }
  have : IsGalois K' E := IsGalois.tower_top_of_isGalois K K' E

  let L' : IntermediateField K E := (IsScalarTower.toAlgHom K L E).fieldRange
  have hsup : K' ⊔ L' = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Algebra.adjoin L ({ζ} : Set E) := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]
      exact le_sup_left (a := K') (mem_adjoin_simple_self K ζ)
    | algebraMap l => exact le_sup_right (b := L') ⟨l, rfl⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hL' : finrank K L' = p := by
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L E)).toLinearEquiv.finrank_eq.symm.trans hL

  have htow1 : finrank K K' * finrank K' E = finrank K E := finrank_mul_finrank K K' E
  have htow2 : finrank K L * finrank L E = finrank K E := finrank_mul_finrank K L E
  have hle : finrank K E ≤ finrank K K' * p := by
    have := finrank_sup_le K' L'
    rwa [hsup, finrank_top', hL'] at this
  have hdeg : finrank K' E = p := by
    have h1 : finrank K' E ≤ p := by
      rw [← htow1] at hle
      exact Nat.le_of_mul_le_mul_left hle hd_pos
    have h2 : p ∣ finrank K K' * finrank K' E := by
      rw [htow1, ← htow2, hL]
      exact dvd_mul_right p _
    have h3 : p ∣ finrank K' E := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h2)
    exact le_antisymm h1 (Nat.le_of_dvd finrank_pos h3)
  have : IsCyclic (E ≃ₐ[K'] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])

  have hE := (enatCard_quotient_le_iff _ p).1 (hR K' E p hp hroots hdeg)

  have hcomap : (ideleClassNorm K' E).range.comap (ideleClassMap K K') ≤
      (ideleClassNorm K L).range := by
    intro c hc
    obtain ⟨y, hy⟩ := hc
    refine mem_of_pow_mem_of_coprime hcop ?_ (hL ▸ pow_finrank_mem_range_ideleClassNorm c)
    refine ⟨ideleClassNorm L E y, ?_⟩
    rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := K'), hy,
      ideleClassNorm_ideleClassMap]
  have := index_le_of_comap_le (ideleClassMap K K') hcomap hE.1
  exact ⟨this.1, this.2.trans hE.2⟩

end PrimeDegree

end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.SecondInequality.Reduction

section

@[expose] public section

namespace GroundTheory.Global

open NumberField Module IntermediateField

universe u

def SecondInequality.{v} : Prop :=
  ∀ (K L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ Module.finrank K L

theorem SecondInequalityRoots.index_le_of_finrank_eq (hR : SecondInequalityRoots.{u}) (n : ℕ) :
    ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], finrank K L = n →
      (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ hn
  have hn0 : 0 < n := hn ▸ finrank_pos
  by_cases h1 : n = 1
  ·
    have htop : (ideleClassNorm K L).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      have := pow_finrank_mem_range_ideleClassNorm (L := L) c
      rwa [hn, h1, pow_one] at this
    rw [htop, Subgroup.index_top]
    omega
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)

  let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers g
  have : H.Normal := ⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩
  let M : IntermediateField K L := fixedField H
  have hML : finrank M L = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have hKM : finrank K M * q = n := by rw [← hML, finrank_mul_finrank, hn]
  have hm_lt : finrank K M < n := by
    have : 0 < finrank K M := finrank_pos
    calc finrank K M < finrank K M * 2 := by omega
      _ ≤ finrank K M * q := Nat.mul_le_mul_left _ hq.two_le
      _ = n := hKM

  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
  have hM := ih (finrank K M) hm_lt K M rfl
  have hL := hR.index_le_of_prime (K := M) (L := L) hq hML

  have hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L :=
    MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c
  have hrange : (ideleClassNorm K L).range =
      (ideleClassNorm M L).range.map (ideleClassNorm K M) := by
    rw [MonoidHom.map_range, hcomp]
  have := index_map_le (ideleClassNorm K M) hL.1 hM.1
  rw [hrange]
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hKM]
  exact Nat.mul_le_mul hM.2 hL.2

theorem SecondInequalityRoots.secondInequality (hR : SecondInequalityRoots.{u}) :
    SecondInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  exact (enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)

end GroundTheory.Global
end
end
