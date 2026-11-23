module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassSplit
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
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLevels
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
public import GroundTheory.ProfiniteCohomology.PoincareDuality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

def openSubgroupMap (U : OpenSubgroup K.1.fixingSubgroup) : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  ⟨(U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype, by
    have hK : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
    have := hK.isOpenMap_subtype_val _ U.isOpen
    convert this using 1
    ext x
    simp⟩

def fieldOf (U : OpenSubgroup K.1.fixingSubgroup) : FiniteSubfield :=
  ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup = (U : Subgroup K.1.fixingSubgroup).map K.1.fixingSubgroup.subtype :=
  fixingSubgroup_ofOpenSubgroup (openSubgroupMap U)

theorem fixingSubgroup_fieldOf_le (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup ≤ K.1.fixingSubgroup := by
  rw [fixingSubgroup_fieldOf]
  rintro _ ⟨g, _, rfl⟩
  exact g.2

theorem subgroupOf_fieldOf (U : OpenSubgroup K.1.fixingSubgroup) :
    (fieldOf U).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup = U := by
  rw [fixingSubgroup_fieldOf, Subgroup.subgroupOf]
  exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _

theorem fieldOf_le_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) : fieldOf U ≤ fieldOf V := by
  have hle : (fieldOf V).1.fixingSubgroup ≤ (fieldOf U).1.fixingSubgroup := by
    rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf]
    exact Subgroup.map_mono h
  have h' := IntermediateField.fixedField_antitone hle
  rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h'

def openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : (U : Subgroup K.1.fixingSubgroup) ≃* (fieldOf U).1.fixingSubgroup :=
  (MulEquiv.subgroupCongr (subgroupOf_fieldOf U).symm).trans
    (Subgroup.subgroupOfEquivOfLe (fixingSubgroup_fieldOf_le U))

theorem continuous_openEquiv (U : OpenSubgroup K.1.fixingSubgroup) : Continuous (openEquiv U).toMonoidHom :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem continuous_openEquiv_symm (U : OpenSubgroup K.1.fixingSubgroup) :
    Continuous (openEquiv U).symm.toMonoidHom :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

def classOpenMor (U : OpenSubgroup K.1.fixingSubgroup) :
    Rep.res (openEquiv U).symm.toMonoidHom (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) ⟶
      classLimitRep (fieldOf U) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def classOpenIso (U : OpenSubgroup K.1.fixingSubgroup) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup K.1.fixingSubgroup).subtype (classLimitRep K)) n ≅
      cohomology (classLimitRep (fieldOf U)) n :=
  haveI := isIso_cohomologyMapAlong_of_mulEquiv (openEquiv U).symm (continuous_openEquiv_symm U)
    (continuous_openEquiv U) (classOpenMor U) Function.bijective_id n
  asIso (cohomologyMapAlong (openEquiv U).symm.toMonoidHom (continuous_openEquiv_symm U) (classOpenMor U) n)

theorem cohomologyResLE_classOpenIso {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) (n : ℕ) :
    haveI : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    cohomologyResLE (classLimitRep K) (show (V : Subgroup K.1.fixingSubgroup) ≤ U from h) n ≫
        (classOpenIso V n).hom =
      (classOpenIso U n).hom ≫ classResField (fieldOf U) (fieldOf V) n := by
  have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
  rw [classOpenIso, classOpenIso, asIso_hom, asIso_hom, cohomologyResLE, classResField,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => Subtype.ext (Subtype.ext rfl)) (fun _ => rfl) n

theorem relIndex_eq_finrank_fieldOf {U V : OpenSubgroup K.1.fixingSubgroup} (h : V ≤ U) :
    letI := algebraOfLE (fieldOf_le_fieldOf h)
    (V : Subgroup K.1.fixingSubgroup).relIndex U = Module.finrank (fieldOf U).1 (fieldOf V).1 := by
  have := relIndex_fixingSubgroup (fieldOf_le_fieldOf h)
  rw [fixingSubgroup_fieldOf, fixingSubgroup_fieldOf,
    Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective] at this
  exact this

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassFormationGlobal

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

noncomputable section

def SumInvRestriction : Prop :=
  ∀ (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K) (ιF : LocalEmbeddings F)
    (y : cohomology (limitRep K) 2),
    idelesSumInv ιF ((idelesResField K F 2).hom y) = Module.finrank K.1 F.1 • idelesSumInv ιK y

theorem idelesToClasses_unitsToIdeles (K : FiniteSubfield) (x : cohomology (unitsLimitRep K) 2) :
    (idelesToClasses K 2).hom ((unitsToIdeles K 2).hom x) = 0 := by
  have h := cohomologyMap_f_comp_g (S := idelesShortComplexRes K) 2
  exact congrArg (fun f => f.hom x) h

section Split

variable (K F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem classResField_classLevelInfl (y : cohomology (ideleClassRep K.1 F.1) 2) :
    (classResField K F 2).hom ((classLevelInfl K F 2).hom y) = 0 := by
  have : IsGalois K.1 F.1 := isGalois_of_normal
  have hle : F.1.fixingSubgroup ≤ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ F)
  have : DiscreteTopology (K.1.fixingSubgroup ⧸ F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) :=
    QuotientGroup.discreteTopology (F.1.fixingSubgroup_isOpen.preimage continuous_subtype_val)
  have hfac : classLevelInfl K F 2 =
      cohomologyMapAlong (quotGalEquiv K F).toMonoidHom continuous_of_discreteTopology (classInvMor K F) 2 ≫
        cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 := by
    rw [classLevelInfl, cohomologyInfl_eq, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => rfl) (fun _ => rfl) 2
  have h0 : (cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom
      ((classLevelInfl K F 2).hom y) = 0 := by
    have h : cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 = 0 :=
      cohomologyInfl_comp_cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 1
    rw [hfac, ModuleCat.hom_comp, LinearMap.comp_apply]
    show ((cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom _) = 0
    rw [h]
    rfl
  exact (cohomologyResLE_apply_eq_zero_iff hle classRep 2 _).2 h0

end Split

variable (hR : SumInvRestriction)


include hR in
theorem idelesToClasses_surjective_of (K : FiniteSubfield) (ι : LocalEmbeddings K) :
    Function.Surjective (idelesToClasses K 2).hom := by
  classical
  intro c
  obtain ⟨p, z, rfl⟩ := exists_classLevelInfl_eq 2 c
  have : IsGalois K.1 p.1.1 := isGalois_of_normal
  obtain ⟨ιF⟩ := nonempty_localEmbeddings p.1
  set N := Module.finrank K.1 p.1.1 with hN
  have hN0 : N ≠ 0 := Module.finrank_pos.ne'
  have hM : Nat.card (LinearMap.ker (classResField K p.1 2).hom) ∣ N := natCard_ker_classResField_dvd K p.1
  obtain ⟨D, hD⟩ := sumPlaceInv_surjective K (QZ.mk (1 / N))
  set Y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D with hYdef
  have hY : idelesSumInv ι Y = QZ.mk (1 / N) := by
    rw [idelesSumInv_apply, hYdef, AddEquiv.apply_symm_apply, hD]
  have hT : ∀ k : ℕ, idelesSumInv ι (k • Y) = QZ.mk ((k : ℚ) / N) := by
    intro k
    rw [map_nsmul, hY, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]
  have hmem : ∀ k : ℕ, (idelesToClasses K 2).hom (k • Y) ∈ LinearMap.ker (classResField K p.1 2).hom := by
    intro k
    rw [LinearMap.mem_ker, ← idelesToClasses_idelesResField]
    have hres : idelesSumInv ιF ((idelesResField K p.1 2).hom (k • Y)) = 0 := by
      rw [hR K p.1 ι ιF, hT, ← QZ.mk_nsmul, nsmul_eq_mul, QZ.mk_eq_zero_iff]
      refine ⟨k, ?_⟩
      have : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
      rw [← hN]
      field_simp
      push_cast
      ring
    obtain ⟨x, hx⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ιF _ hres
    rw [← hx, idelesToClasses_unitsToIdeles]
  let f : Fin N → LinearMap.ker (classResField K p.1 2).hom := fun k =>
    ⟨(idelesToClasses K 2).hom ((k : ℕ) • Y), hmem k⟩
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 : (idelesToClasses K 2).hom ((k : ℕ) • Y) = (idelesToClasses K 2).hom ((k' : ℕ) • Y) :=
      congrArg Subtype.val hkk
    have key : ∀ a b : Fin N, (b : ℕ) ≤ a →
        (idelesToClasses K 2).hom ((a : ℕ) • Y) = (idelesToClasses K 2).hom ((b : ℕ) • Y) → a = b := by
      intro a b hba hab
      have hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Y) = 0 := by
        rw [sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]
      have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw
      rw [hT] at h2
      have := eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)
      exact Fin.ext (by omega)
    rcases le_total (k' : ℕ) k with h | h
    · exact key k k' h h1
    · exact (key k' k h h1.symm).symm
  have hfin : Finite (LinearMap.ker (classResField K p.1 2).hom) :=
    Nat.finite_of_card_ne_zero (fun h0 => hN0 (by rw [h0, zero_dvd_iff] at hM; exact hM))
  have hcardFin : Nat.card (Fin N) = N := Nat.card_eq_fintype_card.trans (Fintype.card_fin N)
  have fsurj := (finj.bijective_of_nat_card_le (by
    rw [hcardFin]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hM)).2
  obtain ⟨k, hk⟩ := fsurj ⟨(classLevelInfl K p.1 2).hom z, classResField_classLevelInfl K p.1 z⟩
  exact ⟨(k : ℕ) • Y, congrArg Subtype.val hk⟩

def classInv (K : FiniteSubfield) (ι : LocalEmbeddings K) : cohomology (classLimitRep K) 2 →+ QZ :=
  (QuotientAddGroup.lift (idelesToClasses K 2).hom.toAddMonoidHom.ker (idelesSumInv ι)
    fun y hy => idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι y hy).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm.toAddMonoidHom

theorem classInv_idelesToClasses (K : FiniteSubfield) (ι : LocalEmbeddings K) (y : cohomology (limitRep K) 2) :
    classInv hR K ι ((idelesToClasses K 2).hom y) = idelesSumInv ι y := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm ((idelesToClasses K 2).hom y) =
      (QuotientAddGroup.mk y : _ ⧸ (idelesToClasses K 2).hom.toAddMonoidHom.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [classInv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

theorem classInv_bijective (K : FiniteSubfield) (ι : LocalEmbeddings K) : Function.Bijective (classInv hR K ι) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ι c
    rw [classInv_idelesToClasses] at hc
    obtain ⟨x, rfl⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι y hc
    exact idelesToClasses_unitsToIdeles K x
  · intro q
    obtain ⟨D, hD⟩ := sumPlaceInv_surjective K q
    refine ⟨(idelesToClasses K 2).hom ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D), ?_⟩
    rw [classInv_idelesToClasses, idelesSumInv_apply, AddEquiv.apply_symm_apply, hD]

theorem classInv_classResField (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K)
    (ιF : LocalEmbeddings F) (c : cohomology (classLimitRep K) 2) :
    classInv hR F ιF ((classResField K F 2).hom c) = Module.finrank K.1 F.1 • classInv hR K ιK c := by
  obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ιK c
  rw [← idelesToClasses_idelesResField, classInv_idelesToClasses, classInv_idelesToClasses, hR K F ιK ιF]

def globalClassFormationOf (K : FiniteSubfield) : ClassFormation (classLimitRep K) where
  inv U := (classInv hR (fieldOf U) (Classical.choice (nonempty_localEmbeddings _))).comp
    (classOpenIso U 2).hom.hom.toAddMonoidHom
  isZero_H1_open_subgroups U := (isZero_cohomology_one_classLimitRep (fieldOf U)).of_iso (classOpenIso U 1)
  inv_res U V h x := by
    have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    have hsq := congrArg (fun f => f.hom x) (cohomologyResLE_classOpenIso h 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hsq, classInv_classResField, relIndex_eq_finrank_fieldOf h]
  inv_bijective U := (classInv_bijective hR _ _).comp
    ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SubsingletonCohomologyThreeInfiniteDecomposition

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit DirectSum groupCohomology

open scoped Pointwise NumberField.LiesOver

noncomputable section

section Infinite

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]


include v in
theorem subsingleton_groupCohomology_one_infiniteDecomposition :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 1) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ c : groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 1, c = 0 by rw [h a, h b]
  intro c
  refine H1_induction_on c fun x => (H1π_eq_zero_iff _).2 ?_
  have hc := isMulCocycle₁_of_mem_cocycles₁ _ x.2
  let e := infiniteDecompositionMulEquiv v w
  let f : Gal(w.Completion/v.Completion) → (w.Completion)ˣ := fun τ => Additive.toMul (x (e.symm τ))
  have hf : IsMulCocycle₁ f := fun τ₁ τ₂ => by
    have h1 := hc (e.symm τ₁) (e.symm τ₂)
    simp only [f, map_mul]
    refine h1.trans ?_
    congr 1
    apply Units.ext
    exact congrArg (fun τ : Gal(w.Completion/v.Completion) =>
      τ ((Additive.toMul (α := (w.Completion)ˣ) (x (e.symm τ₂)) : (w.Completion)ˣ) : w.Completion))
      (e.apply_symm_apply τ₁)
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine (coboundariesOfIsMulCoboundary₁ (G := MulAction.stabilizer Gal(L/K) w)
    (M := (w.Completion)ˣ) (f := fun σ => Additive.toMul (x σ)) ⟨β, fun σ => ?_⟩).2
  have h := hβ (e σ)
  simp only [f, MulEquiv.symm_apply_apply] at h
  refine Eq.trans ?_ h
  congr 1


include v in
theorem isCyclic_infiniteDecomposition : IsCyclic (MulAction.stabilizer Gal(L/K) w) := by
  have h := natCard_infiniteDecompositionGroup v w
  rcases Nat.lt_or_ge (Module.finrank v.Completion w.Completion) 2 with h2 | h2
  · have h1 : Nat.card (MulAction.stabilizer Gal(L/K) w) ≤ 1 := by omega
    have : Subsingleton (MulAction.stabilizer Gal(L/K) w) :=
      (Finite.card_le_one_iff_subsingleton).1 h1
    exact isCyclic_of_subsingleton
  · have hle : Module.finrank v.Completion w.Completion ≤ 2 := by
      have hc := NumberField.InfinitePlace.card_stabilizer (k := K) (w := w)
      rw [← h, hc]
      split_ifs <;> omega
    have h2' : Nat.card (MulAction.stabilizer Gal(L/K) w) = 2 := by omega
    exact isCyclic_of_prime_card (p := 2) h2'


include v in

theorem subsingleton_cohomology_three_infiniteDecomposition :
    Subsingleton (cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 3) := by
  classical
  haveI := isCyclic_infiniteDecomposition v w
  letI : CommGroup (MulAction.stabilizer Gal(L/K) w) := IsCyclic.commGroup
  haveI : Fintype (MulAction.stabilizer Gal(L/K) w) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w)
  haveI := subsingleton_groupCohomology_one_infiniteDecomposition v w
  let A := Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) (w.Completion)ˣ
  let e : cohomology A 3 ≅ groupCohomology A 1 :=
    cohomologyIsoGroupCohomology A 3 ≪≫ Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 3 ⟨1, rfl⟩ ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 ⟨0, rfl⟩).symm
  exact e.toLinearEquiv.injective.subsingleton

end Infinite

section Global

theorem subsingleton_cohomology_three_galUnitsZ_adicCompletion {K : FiniteSubfield}
    (v : HeightOneSpectrum (𝓞 K.1)) :
    Subsingleton (cohomology (galUnitsZ (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))) 3) := by
  have h1 := subsingleton_cohomology_three_galUnits_open (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)) ⊤
  have h2 : Subsingleton (cohomology (galUnits.{0} (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))) 3) :=
    (bijective_cohomologyRes_top _ 3).1.subsingleton
  exact (cohomologyULiftIntAddEquiv (galUnits.{0} (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))) 3).symm.injective.subsingleton

variable {K : FiniteSubfield}

theorem subsingleton_localGaloisCohomology_three (ι : LocalEmbeddings K) (v : Place K.1) :
    Subsingleton (localGaloisCohomology K 3 v) := by
  rcases v with v | v
  · have key : ∀ t : localGaloisCohomology K 3 (.inl v), t = 0 := fun t => by
      obtain ⟨p, z, rfl⟩ := (ι.localLimit 3).exists_infl (.inl v) t
      haveI : (ι.places.inf v p).1.LiesOver v := (ι.places.inf v p).2
      have hs := subsingleton_cohomology_three_infiniteDecomposition (K := K.1) (L := p.1.1) v
        (ι.places.inf v p).1
      have hz : z = 0 := hs.elim _ _
      rw [hz, map_zero]
      rfl
    exact ⟨fun a b => (key a).trans (key b).symm⟩
  · exact subsingleton_cohomology_three_galUnitsZ_adicCompletion v

theorem subsingleton_cohomology_three_limitRep : Subsingleton (cohomology (limitRep K) 3) := by
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  have h : ∀ ζ : ⨁ v : Place K.1, localGaloisCohomology K 3 v, ζ = 0 := fun ζ => by
    ext v
    haveI := subsingleton_localGaloisCohomology_three ι v
    exact Subsingleton.elim _ _
  haveI : Subsingleton (⨁ v : Place K.1, localGaloisCohomology K 3 v) :=
    ⟨fun a b => (h a).trans (h b).symm⟩
  exact (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 3)).injective.subsingleton

end Global

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

noncomputable section

theorem sumInvRestriction : SumInvRestriction :=
  fun _ _ _ ιK ιF y => idelesSumInv_idelesResField ιK ιF y

theorem idelesToClasses_surjective (K : FiniteSubfield) : Function.Surjective (idelesToClasses K 2).hom :=
  idelesToClasses_surjective_of sumInvRestriction K (Classical.choice (nonempty_localEmbeddings K))

def globalClassFormation (K : FiniteSubfield) : ClassFormation (classLimitRep K) :=
  globalClassFormationOf sumInvRestriction K

theorem subsingleton_cohomology_three_unitsLimitRep (K : FiniteSubfield) :
    Subsingleton (cohomology (unitsLimitRep K) 3) := by
  have h3 := subsingleton_cohomology_three_limitRep (K := K)
  refine ⟨fun x x' => ?_⟩
  have hz : ∀ x : cohomology (unitsLimitRep K) 3, x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 2 x (Subsingleton.elim _ _)
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective K c
    exact congrArg (fun f => f.hom y) (comp_δ (idelesShortComplexRes_shortExact K) 2 3 rfl)
  rw [hz x, hz x']

end

end GroundTheory.ProfCoh
end
end
