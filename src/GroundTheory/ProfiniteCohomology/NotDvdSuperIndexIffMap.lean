module

public import GroundTheory.ProfiniteCohomology.OpenNormal
public import GroundTheory.ProfiniteCohomology.Supernatural
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
import GroundTheory.ProfiniteCohomology.OpenNormal
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.CategoryTheory.CofilteredSystem

-- Source module: GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

variable {G : Type*} [Group G]

theorem inf_sup_normal_eq {X H U : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U := by
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _ le_sup_left) (le_inf hUX le_sup_right))
  obtain ⟨hxX, hxHU⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxHU
  have hhX : h ∈ X := by
    have := X.mul_mem hxX (X.inv_mem (hUX hu))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hhX, hh⟩) hu

theorem relIndex_sup_normal_eq {X H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hUX : U ≤ X) :
    X.relIndex (H ⊔ U) = X.relIndex H := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex U X (H ⊔ U)
  have h2 := Subgroup.relIndex_inf_mul_relIndex U X H
  rw [inf_eq_left.mpr hUX, Subgroup.relIndex_sup_right, inf_sup_normal_eq hUX,
    Subgroup.relIndex_sup_right] at h1
  rw [inf_eq_left.mpr hUX] at h2
  have hne : U.relIndex (X ⊓ H) ≠ 0 := fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal U (X ⊓ H)))
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)

theorem index_sup_normal_eq_mul {K H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hKH : K ≤ H) :
    (K ⊔ U).index = (H ⊔ U).index * (K ⊔ U).relIndex H := by
  rw [← Subgroup.relIndex_mul_index (sup_le_sup_right hKH U),
    relIndex_sup_normal_eq (le_sup_right : U ≤ K ⊔ U), mul_comm]

theorem sup_subgroupOf_eq {K H U : Subgroup G} [U.Normal] (hKH : K ≤ H) :
    (K ⊔ U).subgroupOf H = K.subgroupOf H ⊔ U.subgroupOf H := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_left : K ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_right : U ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx))))
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hkH : k ∈ H := hKH hk
  have huH : u ∈ H := by
    have := H.mul_mem (H.inv_mem hkH) x.2
    rwa [← hku, inv_mul_cancel_left] at this
  have hx' : x = ⟨k, hkH⟩ * ⟨u, huH⟩ := Subtype.ext hku.symm
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk) (Subgroup.mem_subgroupOf.mpr hu)

variable [TopologicalSpace G]

noncomputable def superIndex (H : Subgroup G) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat (H ⊔ (U : Subgroup G)).index

noncomputable def superRelIndex (K H : Subgroup G) : Supernatural :=
  superIndex (K.subgroupOf H)

variable [IsTopologicalGroup G] [CompactSpace G]

instance OpenNormalSubgroup.finiteIndex (U : OpenNormalSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

theorem index_sup_ne_zero (H : Subgroup G) (U : OpenNormalSubgroup G) :
    (H ⊔ (U : Subgroup G)).index ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_right))

theorem relIndex_sup_ne_zero (K H : Subgroup G) (U : OpenNormalSubgroup G) :
    (K ⊔ (U : Subgroup G)).relIndex H ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ (Subgroup.relIndex_dvd_of_le_left H le_sup_right).trans
      (Subgroup.relIndex_dvd_index_of_normal (U : Subgroup G) H)))

theorem ofNat_index_sup_antitone (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Supernatural.ofNat (H ⊔ (V : Subgroup G)).index ≤
      Supernatural.ofNat (H ⊔ (U : Subgroup G)).index := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V)
    (index_sup_ne_zero H U)]
  exact Subgroup.index_dvd_of_le (sup_le_sup_left (fun x hx => h hx) H)

theorem ofNat_relIndex_sup_antitone (K H : Subgroup G) {U V : OpenNormalSubgroup G}
    (h : U ≤ V) :
    Supernatural.ofNat ((K ⊔ (V : Subgroup G)).relIndex H) ≤
      Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (relIndex_sup_ne_zero K H V)
    (relIndex_sup_ne_zero K H U)]
  exact Subgroup.relIndex_dvd_of_le_left H (sup_le_sup_left (fun x hx => h hx) K)

theorem not_dvd_superIndex_iff (p : Nat.Primes) (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ (p : ℕ) ∣ (H ⊔ (U : Subgroup G)).index := by
  rw [superIndex, Supernatural.ofNat_prime_dvd_iSup_iff, not_exists]
  refine forall_congr' fun U => ?_
  rw [Supernatural.ofNat_dvd_ofNat p.prop.ne_zero (index_sup_ne_zero H U)]

theorem superRelIndex_eq_iSup [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superRelIndex K H =
      ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by

  let res : OpenNormalSubgroup G → OpenNormalSubgroup H := fun U =>
    { toSubgroup := (U : Subgroup G).subgroupOf H
      isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
      isNormal' := inferInstance }
  have hres : ∀ U : OpenNormalSubgroup G,
      K.subgroupOf H ⊔ ((res U : OpenNormalSubgroup H) : Subgroup H) =
        (K ⊔ (U : Subgroup G)).subgroupOf H :=
    fun U => (sup_subgroupOf_eq hKH).symm
  refine le_antisymm (iSup_le fun V => ?_) (iSup_le fun U => ?_)
  ·
    obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
    have h1W : (1 : G) ∈ W := by
      have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
      simpa using this
    obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
    refine le_iSup_of_le U ?_
    have hle : (K ⊔ (U : Subgroup G)).subgroupOf H ≤ K.subgroupOf H ⊔ (V : Subgroup H) := by
      rw [← hres U]
      refine sup_le_sup_left (fun x hx => ?_) _
      have : (x : G) ∈ W := hUW hx
      have : x ∈ Subtype.val ⁻¹' W := this
      rw [hWV] at this
      exact this
    have hne : ((K ⊔ (U : Subgroup G)).subgroupOf H).index ≠ 0 := relIndex_sup_ne_zero K H U
    show Supernatural.ofNat _ ≤ Supernatural.ofNat ((K ⊔ (U : Subgroup G)).subgroupOf H).index
    rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat
      (fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))) hne]
    exact Subgroup.index_dvd_of_le hle
  · refine le_iSup_of_le (res U) ?_
    rw [hres U]
    exact le_rfl

theorem superIndex_of_isOpen [TotallyDisconnectedSpace G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : superIndex H = Supernatural.ofNat H.index := by
  have : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  refine le_antisymm (iSup_le fun V => ?_) (le_iSup_of_le U ?_)
  · rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V) hne]
    exact Subgroup.index_dvd_of_le le_sup_left
  · rw [sup_eq_left.mpr (fun x hx => hU hx)]

theorem superIndex_eq_mul [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex K = superIndex H * superRelIndex K H := by
  rw [superRelIndex_eq_iSup hKH, superIndex, superIndex,
    Supernatural.iSup_mul_iSup fun U V =>
      ⟨U ⊓ V, ofNat_index_sup_antitone H inf_le_left, ofNat_relIndex_sup_antitone K H inf_le_right⟩]
  refine iSup_congr fun U => ?_
  rw [index_sup_normal_eq_mul hKH, Supernatural.ofNat_mul (index_sup_ne_zero H U)
    (relIndex_sup_ne_zero K H U)]

theorem superIndex_dvd_of_le [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex H ∣ superIndex K :=
  ⟨superRelIndex K H, superIndex_eq_mul hKH⟩

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Pointwise CategoryTheory

variable {G : Type*} [Group G]

theorem sup_eq_comap_map (H U : Subgroup G) [U.Normal] :
    H ⊔ U = (H.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem index_sup_eq_index_map (H U : Subgroup G) [U.Normal] :
    (H ⊔ U).index = (H.map (QuotientGroup.mk' U)).index := by
  rw [sup_eq_comap_map, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]

variable [TopologicalSpace G]

noncomputable def quotMap {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) (fun _ hx => h hx)

theorem quotMap_comp_mk' {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (quotMap h).comp (QuotientGroup.mk' (U : Subgroup G)) = QuotientGroup.mk' (V : Subgroup G) :=
  rfl

theorem quotMap_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (quotMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V : Subgroup G) y
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩

theorem quotMap_self {U : OpenNormalSubgroup G} (h : U ≤ U) : quotMap h = MonoidHom.id _ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem quotMap_comp {U V W : OpenNormalSubgroup G} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (quotMap h₂).comp (quotMap h₁) = quotMap (h₁.trans h₂) :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem map_map_quotMap (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (H.map (QuotientGroup.mk' (U : Subgroup G))).map (quotMap h) =
      H.map (QuotientGroup.mk' (V : Subgroup G)) := by
  rw [Subgroup.map_map, quotMap_comp_mk']

def IsProSylow (p : ℕ) (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProPGroup p P ∧ ¬ Supernatural.ofNat p ∣ superIndex P

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]


omit [TotallyDisconnectedSpace G] in
theorem not_dvd_superIndex_iff_map (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ p ∣ (H.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  have h := not_dvd_superIndex_iff (⟨p, hp.out⟩ : Nat.Primes) H
  simp only [index_sup_eq_index_map] at h
  exact h

theorem isProSylow_iff {P : Subgroup G} (hP : IsClosed (P : Set G)) :
    IsProSylow p P ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (P.map (QuotientGroup.mk' (U : Subgroup G))) ∧
        ¬ p ∣ (P.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  rw [IsProSylow, isProPGroup_subgroup_iff_isPGroup_map, not_dvd_superIndex_iff_map, ← forall_and]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩


omit [CompactSpace G] [TotallyDisconnectedSpace G] in
noncomputable def sylowSystem (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    OpenNormalSubgroup G ⥤ Type _ where
  obj U := {S : Sylow p (G ⧸ (U : Subgroup G)) //
    H.map (QuotientGroup.mk' (U : Subgroup G)) ≤ (S : Subgroup (G ⧸ (U : Subgroup G)))}
  map {U V} f := ↾fun S => ⟨S.1.mapSurjective (quotMap_surjective (leOfHom f)), by
    rw [Sylow.coe_mapSurjective, ← map_map_quotMap H (leOfHom f)]
    exact Subgroup.map_mono S.2⟩
  map_id U := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ (S : Subgroup (G ⧸ (U : Subgroup G)))
    rw [quotMap_self, Subgroup.map_id]
  map_comp {U V W} f g := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ ((S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap (leOfHom f))).map
        (quotMap (leOfHom g))
    rw [Subgroup.map_map, quotMap_comp]

theorem exists_isProSylow_le {H : Subgroup G} (hH : IsProPGroup p H) :
    ∃ P : Subgroup G, IsProSylow p P ∧ H ≤ P := by
  rw [isProPGroup_subgroup_iff_isPGroup_map] at hH
  have hfin : ∀ U, Finite ((sylowSystem p H).obj U) := fun U => by
    have := Sylow.finite_of_finiteIndex (default : Sylow p (G ⧸ (U : Subgroup G)))
    exact Subtype.finite
  have hne : ∀ U, Nonempty ((sylowSystem p H).obj U) := fun U => by
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hH U)
    exact ⟨⟨S, hS⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (sylowSystem p H)

  let T : OpenNormalSubgroup G → Subgroup G := fun U =>
    ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).comap (QuotientGroup.mk' (U : Subgroup G))
  have hc : ∀ {U V : OpenNormalSubgroup G} (h : U ≤ V),
      ((s V).1 : Subgroup (G ⧸ (V : Subgroup G))) =
        ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap h) := by
    intro U V h
    rw [← hs (homOfLE h)]
    rfl
  have hHT : ∀ U, H ≤ T U := fun U => Subgroup.map_le_iff_le_comap.mp (s U).2
  have hUT : ∀ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ T U := fun U x hx => by
    show QuotientGroup.mk' (U : Subgroup G) x ∈ ((s U).1 : Subgroup _)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hTcl : ∀ U, IsClosed (T U : Set G) := fun U =>
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (hUT U) U.toOpenSubgroup.isOpen)
  have hTmono : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → T U ≤ T V := fun {U V} h x hx => by
    show QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _)
    rw [hc h]
    exact Subgroup.mem_map_of_mem (quotMap h) hx
  have hTlift : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → ∀ x ∈ T V,
      ∃ y ∈ T U, y⁻¹ * x ∈ (V : Subgroup G) := fun {U V} h x hx => by
    have hx' : QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _) := hx
    rw [hc h] at hx'
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    exact ⟨y, hz, QuotientGroup.eq.mp hzx⟩
  let P : Subgroup G := ⨅ U, T U
  have hPcl : IsClosed (P : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter hTcl
  have hPmap : ∀ U : OpenNormalSubgroup G,
      P.map (QuotientGroup.mk' (U : Subgroup G)) = ((s U).1 : Subgroup _) := by
    intro U
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (iInf_le T U)) fun z hz => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    have hx : x ∈ T U := hz

    let t : OpenNormalSubgroup G → Set G := fun W =>
      (T (W ⊓ U) : Set G) ∩ {y | x⁻¹ * y ∈ (U : Subgroup G)}
    have htcl : ∀ W, IsClosed (t W) := fun W =>
      (hTcl _).inter ((Subgroup.isClosed_of_isOpen _ U.toOpenSubgroup.isOpen).preimage
        (continuous_const_mul x⁻¹))
    have htdir : Directed (· ⊇ ·) t := fun W₁ W₂ =>
      ⟨W₁ ⊓ W₂, fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_left) hy.1, hy.2⟩,
        fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_right) hy.1, hy.2⟩⟩
    have htne : ∀ W, (t W).Nonempty := fun W => by
      obtain ⟨y, hy, hyx⟩ := hTlift (inf_le_right : W ⊓ U ≤ U) x hx
      refine ⟨y, hy, ?_⟩
      have := (U : Subgroup G).inv_mem hyx
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htdir
      htne (fun W => (htcl W).isCompact) htcl
    rw [Set.mem_iInter] at hy
    have hyP : y ∈ P := Subgroup.mem_iInf.mpr fun W => hTmono inf_le_left (hy W).1
    refine Subgroup.mem_map.mpr ⟨y, hyP, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr (hy U).2).symm
  refine ⟨P, (isProSylow_iff hPcl).mpr fun U => ?_, le_iInf fun U => hHT U⟩
  rw [hPmap U]
  exact ⟨(s U).1.isPGroup', (s U).1.not_dvd_index⟩

theorem exists_isProSylow : ∃ P : Subgroup G, IsProSylow p P :=
  let ⟨P, hP, _⟩ := exists_isProSylow_le (isProPGroup_bot (G := G) p)
  ⟨P, hP⟩

end GroundTheory.ProfCoh
end
end
