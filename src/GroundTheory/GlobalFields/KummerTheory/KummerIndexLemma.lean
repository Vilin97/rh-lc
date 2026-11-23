module

public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
public import GroundTheory.GlobalFields.FirstInequalityStatement
public import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom
public import GroundTheory.GlobalFields.KummerTheory.SplittingInfinite
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
public import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.Places
import GroundTheory.GlobalFields.KummerTheory.SplittingKummer
public import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.GlobalFields.SplittingFromInequality
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.KummerTheory.Degree
public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
public import GroundTheory.GlobalFields.ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm
import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
import GroundTheory.GlobalFields.IdeleGroups.IndexFormula
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

-- Source module: GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.PowerKernel

section

@[expose] public section

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh Module
  Filter IntermediateField AdeleBaseChange SemiLocal IdeleNorm

open scoped NumberField.LiesOver

namespace KummerIndex

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem finiteProj_mem_localUnits {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K}
    (h : IdeleGroup.ord v x = 0) : IdeleGroup.finiteProj v x ∈ localUnits v := by
  have hx := (IdeleGroup.ord_eq_zero_iff v x).1 h
  rw [localUnits, Submonoid.mem_units_iff]
  have h2 : ((IdeleGroup.finiteProj v x)⁻¹ : (v.adicCompletion K)ˣ) =
      IdeleGroup.finiteProj v x⁻¹ := (map_inv _ _).symm
  rw [h2, IdeleGroup.coe_finiteProj, IdeleGroup.coe_finiteProj]
  exact hx

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (b : (v.adicCompletion K)ˣ) : b ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  classical
  let y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ := fun w ↦
    Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
      v.adicCompletion K →* w.1.adicCompletion L) b
  refine ⟨y, ?_⟩
  rw [← Finset.univ_prod_mulSingle y, map_prod]
  simp_rw [y, finiteLocalNorm_mulSingle_algebraMap]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_eq]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (w : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L w) : (infiniteLocalNorm L w).range = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨w'⟩ := nonempty_infinitePlacesOver L w
  have hd := (InfinitePlace.splitsCompletely_iff_forall_finrank w).1 h w'
  refine ⟨Pi.mulSingle w' (Units.map (algebraMap w.Completion
    (w' : InfinitePlace L).Completion : w.Completion →* (w' : InfinitePlace L).Completion) u), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  simp [LocalField.normUnits, Algebra.norm_algebraMap, hd]

end LocalNorms

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.mem_unitsPow_of_forall_mem_unitsPowIn
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : (IdeleGroup.diagonal K).range ⊔
      IdeleGroup.sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v))
    {y : Kˣ}
    (hyE : y ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hyS : ∀ v ∈ S, y ∈ unitsPowIn K p (v.adicCompletion K))
    (hyinf : ∀ w : InfinitePlace K, y ∈ unitsPowIn K p w.Completion) :
    y ∈ unitsPow K p := by
  classical
  by_contra hy
  let Ω := AlgebraicClosure K
  let F := kummerExtension K p Ω (radicalGroup K p y)
  have hfinF : finrank K F = p := finrank_kummerExtension_radicalGroup Ω hy
  have : IsCyclic Gal(F/K) := isCyclic_kummerExtension_radicalGroup Ω hy
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω y
  have hgen : IntermediateField.adjoin K {α} = ⊤ := by
    have hdvd : finrank K (IntermediateField.adjoin K {α}) ∣ p := by
      have := IntermediateField.finrank_dvd_of_le_right (K := K)
        (le_top : IntermediateField.adjoin K {α} ≤ ⊤)
      rwa [IntermediateField.finrank_top', hfinF] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hpp
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h1
      have hmem : α ∈ (⊥ : IntermediateField K F) :=
        h1 ▸ IntermediateField.mem_adjoin_simple_self K α
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
      have hcp : c ^ p = (y : K) := by
        apply (algebraMap K F).injective
        rw [map_pow, hc, hα]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow (Fact.out : p.Prime).ne_zero] at hcp
        exact y.ne_zero hcp.symm
      exact hy (mem_unitsPow.2 ⟨Units.mk0 c hc0, Units.ext (by simp [hcp])⟩)
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hpp, IntermediateField.finrank_top', hfinF])
  suffices h : (ideleNorm K F).range ⊔ (IdeleGroup.diagonal K).range = ⊤ by
    have h1 := hFI.finrank_eq_one_of_sup_eq_top h
    rw [hfinF] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hsplit : ∀ v ∈ S, (finiteLocalNorm F v).range = ⊤ := fun v hv ↦
    range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
      ((splitsCompletely_kummerExtension_iff v).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyS v hv) (unitsPow_le_unitsPowIn K p _) hc)))
  have hinf : ∀ w, (infiniteLocalNorm F w).range = ⊤ := fun w ↦
    range_infiniteLocalNorm_eq_top_of_splitsCompletely w
      ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyinf w) (unitsPow_le_unitsPowIn K p _) hc))
  have hunr : ∀ v, v ∉ S → v ∉ T →
      (integerUnitsOver F v).map (finiteLocalNorm F v) = localUnits v := by
    intro v hvS hvT
    obtain ⟨w⟩ := nonempty_placesOver F v
    have := w.1.isPrime
    refine map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w ?_
    refine Kummer.ramificationIdx_eq_one_of_pow_eq y hα hgen v (fun h ↦ hvS (hpS v h)) ?_
      w.1.asIdeal
    rw [valuation_eq_one_of_mem_unit hyE (by simp [hvS, hvT]), WithZero.log_one]
    exact dvd_zero _
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, s, hs, rfl⟩ := IdeleGroup.exists_diagonal_mul_of_sup_eq_top _ hS x
  have hsv : ∀ v ∉ S, IdeleGroup.finiteProj v s ∈ localUnits v := fun v hv ↦
    finiteProj_mem_localUnits ((IdeleGroup.mem_sIdeles _).1 hs v (by simpa using hv))
  obtain ⟨δ, hδ, hδT⟩ := hsurj (fun v ↦ IdeleGroup.finiteProj v s)
    (fun v hv ↦ hsv v (Finset.disjoint_right.1 hST hv))
  set t := IdeleGroup.diagonal K δ⁻¹ * s with ht_def
  have hloc : ∀ v, v ∉ S → IdeleGroup.finiteProj v t ∈ localUnits v := by
    intro v hvS
    rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal]
    exact mul_mem (units_map_mem_localUnits v (valuation_eq_one_of_mem_unit (inv_mem hδ)
      (by simpa using hvS))) (hsv v hvS)
  have ht : t ∈ (ideleNorm K F).range := by
    rw [mem_range_ideleNorm_iff]
    refine ⟨fun v ↦ ?_, fun w ↦ by rw [hinf w]; exact Subgroup.mem_top _, ?_⟩
    · by_cases hvS : v ∈ S
      · rw [hsplit v hvS]
        exact Subgroup.mem_top _
      by_cases hvT : v ∈ T
      · have hpow : IdeleGroup.finiteProj v t ∈ unitsPow (v.adicCompletion K) p := by
          rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal, map_inv]
          exact QuotientGroup.eq.1 (hδT v hvT)
        obtain ⟨b, hb⟩ := mem_unitsPow.1 hpow
        have hnorm := pow_finrank_mem_range_finiteLocalNorm (L := F) v b
        rw [hfinF, hb] at hnorm
        exact hnorm
      · exact Subgroup.map_le_range _ _ (hunr v hvS hvT ▸ hloc v hvS)
    · filter_upwards [(S.finite_toSet.union T.finite_toSet).eventually_cofinite_notMem] with v hv
      simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
      rw [hunr v hv.1 hv.2]
      exact hloc v hv.1
  have hs_eq : s = t * IdeleGroup.diagonal K δ := by
    rw [ht_def, map_inv, mul_comm, mul_inv_cancel_left]
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ⟨δ, rfl⟩))

end KummerIndex

end GroundTheory.Global
end
end
end

-- Source module: GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma

section

@[expose] public section

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh IdeleGroup

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

theorem mem_unit_of_pow_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} (hp : p ≠ 0) {b : Kˣ}
    (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have he : v.valuationOfNeZero (b ^ p) = 1 := by
    have h := hb v hv
    rw [← valuationOfNeZero_eq] at h
    exact_mod_cast h
  rw [map_pow] at he
  rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 he).resolve_right hp, WithZero.coe_one]

theorem unitsPow_subgroupOf_unit (S : Set (HeightOneSpectrum (𝓞 K))) (hp : p ≠ 0) :
    (unitsPow K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, mem_unit_of_pow_mem_unit hp (hb ▸ e.2)⟩, Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem relIndex_powerSubgroup_eq_pow [NeZero p] [HasEnoughRootsOfUnity K p]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) T).relIndex
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  rw [relIndex_powerSubgroup, ← relIndex_powerSubgroup_empty, relIndex_powerSubgroup_empty_eq_pow S hpS]

universe u

variable {K : Type u} [Field K] [NumberField K] [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.comap_sUnitsToSIdeles_powerSubgroup_union
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v)) :
    ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T))).comap
          (sUnitsToSIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (powMonoidHom p : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K →* _).range := by
  ext e
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_sUnitsToSIdeles, powerSubgroup,
    mem_localSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨hf, hi, -⟩
    have hy := hFI.mem_unitsPow_of_forall_mem_unitsPowIn S T hST hpS hJ hsurj e.2
      (fun v hv ↦ by
        obtain ⟨u, hu⟩ := hf v hv
        refine mem_unitsPowIn.2 ⟨(u : v.adicCompletion K), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, finiteProj_diagonal]
        rfl)
      (fun w ↦ by
        obtain ⟨u, hu⟩ := hi w
        refine mem_unitsPowIn.2 ⟨(u : w.Completion), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, infiniteProj_diagonal]
        rfl)
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hy
    refine ⟨⟨b, mem_unit_of_pow_mem_unit (Fact.out : p.Prime).ne_zero (hb ▸ e.2)⟩,
      Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    refine ⟨fun v _ ↦ ⟨finiteProj v (diagonal K f), ?_⟩,
      fun w ↦ ⟨infiniteProj w (diagonal K f), ?_⟩, fun v hv ↦ ?_⟩
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · exact (diagonal_mem_sIdeles_iff _ _).2 (powMonoidHom p f).2 v hv

theorem card_add_one_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p)
    (haT : ∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K))
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card)
    (hker : ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
      x ∈ radicalGroup K p a) :
    T.card + 1 = S.card + Fintype.card (InfinitePlace K) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hΔp : (unitsPow K p).relIndex Δ = p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [Subgroup.relIndex, unitsPow_subgroupOf_unit _ (Fact.out : p.Prime).ne_zero,
      SUnit.index_range_powMonoidHom]
    simp
  have heq : radicalGroup K p a ⊓ Δ = unitsPowAt p T ⊓ Δ := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨radicalGroup_le (mem_unitsPowAt.2 haT) (unitsPow_le_unitsPowAt p T) h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hker x h2 h1, h2⟩
  have hrad : (radicalGroup K p a).relIndex Δ = p ^ T.card := by
    rw [← Subgroup.inf_relIndex_right, heq, Subgroup.inf_relIndex_right, hidx]
  have hstep : (unitsPow K p).relIndex (radicalGroup K p a ⊓ Δ) = p := by
    rw [← QuotientGroup.ker_mk' (unitsPow K p), Subgroup.relIndex_ker]
    set H := (radicalGroup K p a ⊓ Δ).map (QuotientGroup.mk' (unitsPow K p))
    have hle : H ≤ Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) a) := by
      rw [← radicalClasses_radicalGroup]
      exact Subgroup.map_mono inf_le_left
    have hord : orderOf (QuotientGroup.mk' (unitsPow K p) a) = p := by
      refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
      rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hdvd : Nat.card H ∣ p := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
    · exfalso
      have hbot := Subgroup.card_eq_one.1 h1
      have hmem : QuotientGroup.mk' (unitsPow K p) a ∈ H :=
        Subgroup.mem_map_of_mem _ ⟨mem_radicalGroup_self a, ha⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hap hmem
    · exact hp
  have h := Subgroup.relIndex_inf_mul_relIndex (unitsPow K p) (radicalGroup K p a) Δ
  rw [inf_of_le_left (unitsPow_le_radicalGroup a), hstep, hrad, hΔp, ← pow_succ'] at h
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  omega

theorem _root_.GroundTheory.Global.FirstInequality.exists_places_index_map_powerSubgroup
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    {a : Kˣ} (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      T.card + 1 = S.card + Fintype.card (InfinitePlace K) ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K)).index = p := by
  classical
  obtain ⟨T, hST, haT, hidx, hker⟩ := hFI.exists_places_unitsPowAt S hpS ha
  have hcard := card_add_one_eq S T ha hap haT hidx hker
  refine ⟨T, hST, hcard, haT, ?_⟩
  have hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal := fun v hv h ↦
    Finset.disjoint_right.1 hST hv (hpS v h)
  have hsurj := exists_localClass_eq S T hST hpT hidx
  set S' : Set (HeightOneSpectrum (𝓞 K)) := (S : Set (HeightOneSpectrum (𝓞 K))) ∪ T with hS'
  have hJ' : (diagonal K).range ⊔ sIdeles S' = ⊤ :=
    sup_sIdeles_eq_top_of_subset Set.subset_union_left hJ
  set W := (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
    (sIdeles S')
  have hle : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      sIdeles S' :=
    powerSubgroup_le_sIdeles _ _ p
  have hmap : W.map (sIdelesToIdeleClassGroup S') =
      (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K) := by
    rw [sIdelesToIdeleClassGroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle]
  have hW : W.index = p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) :=
    relIndex_powerSubgroup_eq_pow S T hpS
  have hcardS' : Nat.card S' = S.card + T.card := by
    rw [hS', ← Finset.coe_union, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_union_of_disjoint hST]
  have hE : (W.comap (sUnitsToSIdeles S')).index =
      p ^ (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by
    rw [hFI.comap_sUnitsToSIdeles_powerSubgroup_union S T hST hpS hJ hsurj,
      SUnit.index_range_powMonoidHom, hcardS']
  have h := index_map_mul_index_comap S' hJ' W
  rw [hmap, hE, hW] at h
  have h2 : 2 * (S.card + Fintype.card (InfinitePlace K)) =
      1 + (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by omega
  rw [h2, pow_add p 1, pow_one] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) h

end KummerIndex

end GroundTheory.Global
end
end
end
