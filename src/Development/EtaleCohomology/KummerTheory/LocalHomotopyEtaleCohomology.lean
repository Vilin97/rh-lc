module

public import Development.EtaleCohomology.KummerTheory.DictNormalPf
public import Development.EtaleCohomology.KummerTheory.InjSlicePf
public import Development.EtaleCohomology.KummerTheory.ContCut
public import Development.EtaleCohomology.KummerTheory.LocCokPf
public import Development.EtaleCohomology.KummerExtensions.EtaleLefschetzHochschildSectionOfCupSchemaAndKum
public import Development.EtaleCohomology.KummerTheory.AffRingPf
public import Development.EtaleCohomology.KummerTheory.BcHomIsPullback
public import Development.EtaleCohomology.KummerTheory.CokAffPf
public import Development.EtaleCohomology.KummerTheory.ConeAlgPf
public import Development.EtaleCohomology.KummerTheory.FinalTheorems
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
import Mathlib.Tactic.Lemma
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
public import Development.EtaleCohomology.KummerTheory.ConeObjPf
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Development.EtaleCohomology.KummerTheory.CupAWCut
public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.DeltaPf
public import Development.EtaleCohomology.KummerTheory.DictExistPf
import Development.EtaleCohomology.KummerTheory.DictPfEv
public import Development.EtaleCohomology.KummerTheory.DictZeroPf
public import Development.EtaleCohomology.KummerTheory.EtaleLerayHirschConeSourceComponentVanishesAfter
public import Development.EtaleCohomology.KummerTheory.ExIsoPf
public import Development.EtaleCohomology.KummerTheory.ExactPf
public import Development.EtaleCohomology.KummerTheory.FivePf
public import Development.EtaleCohomology.KummerTheory.FlasquePf
public import Development.EtaleCohomology.KummerTheory.ForgetInjPf
public import Development.EtaleCohomology.KummerTheory.GhostPf
public import Development.EtaleCohomology.KummerTheory.GluePf
public import Development.EtaleCohomology.KummerTheory.HomKillPf
public import Development.EtaleCohomology.KummerTheory.ISupFinSuccEq
import Development.EtaleCohomology.KummerTheory.LHCutGlue
public import Development.EtaleCohomology.KummerTheory.LimOfIso
public import Development.EtaleCohomology.KummerTheory.LocKerPf
public import Development.EtaleCohomology.KummerTheory.MVnatPf
public import Development.EtaleCohomology.KummerTheory.NrmMkPf
public import Development.EtaleCohomology.KummerTheory.SHenCutPf

-- Source module: Development.EtaleCohomology.KummerTheory.ConeCxPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def shvHomOf {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F G : SlShv Λ S)
    (f : ∀ U : Over S, F.obj.obj (op U) →ₗ[ULift.{1} Λ] G.obj.obj (op U))
    (hf : ∀ (V U : Over S) (g : V ⟶ U) x, f V ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom (f U x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom (f U.unop)
     naturality := by intro U V g; ext x; exact hf V.unop U.unop g.unop x }⟩

lemma sec_sub {Λ : Type} [CommRing Λ] {F : Shv Λ} (hF : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor
  intro a b
  have h := hF.eq_of_src (𝟙 F) 0
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, h]
  rfl

lemma isZero_of_sub {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F : SlShv Λ S)
    (h : ∀ U : Over S, Subsingleton (F.obj.obj (op U))) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

theorem coneCx_of (h1 : ConeObj) (h2 : ConeAlg) : ConeCx := by
  intro Λ _ I J K μ hJ hK X S p r M γ hγ
  choose T hT e he using fun j : ℤ => h1 Λ J K hJ.1 hK.1 p r M j
  have hA := fun j : ℤ => h2 Λ μ p r M γ hγ j (j + 1) rfl
  let D : ∀ (j : ℤ) (U : Over S), (T j).obj.obj (op U) →ₗ[ULift.{1} Λ] (T (j + 1)).obj.obj (op U) :=
    fun j U => (e (j + 1) U).symm.toLinearMap ∘ₗ IsLinearMap.mk' _ (hA j U).1 ∘ₗ (e j U).toLinearMap
  have hD : ∀ (j : ℤ) (U : Over S) x, e (j + 1) U (D j U x) = cD μ p γ j (j + 1) rfl U (e j U x) := by
    intro j U x
    simp [D]
  let d : ∀ j : ℤ, T j ⟶ T (j + 1) := fun j => shvHomOf (T j) (T (j + 1)) (D j) (by
    intro V U g x
    refine (e (j + 1) V).injective ?_
    rw [hD, he, he, hD, ((hA j U).2.2 V g).2.1])
  have sq : ∀ j : ℤ, d j ≫ d (j + 1) = 0 := by
    intro j
    ext U x
    change D (j + 1) U.unop (D j U.unop x) = 0
    refine (e (j + 1 + 1) U.unop).injective ?_
    rw [hD, hD, (hA j U.unop).2.1, map_zero]
  refine ⟨CochainComplex.of T d sq, fun j => hT j, ?_, fun j U => (e j U).toAddEquiv, fun j V U g x => he j V U g x, ?_⟩
  · intro j hj
    apply isZero_of_sub
    intro U
    have : Subsingleton (Cone J K p r M j U) := by
      have h3 : ∀ (a : Fin (M + 1)) (s : Fin (r a)), Subsingleton (Sec (J.X (j + 1 - ((a : ℕ) : ℤ))) U.left) :=
        fun a s => sec_sub (hJ.2 _ (by omega)) _
      have h4 : Subsingleton (Sec (K.X j) (pullback p U.hom)) := sec_sub (hK.2 _ (by omega)) _
      constructor
      intro x y
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext a s
      exact (h3 a s).elim _ _
    exact (e j U).injective.subsingleton
  · intro j j' h U x
    subst h
    have hd : (CochainComplex.of T d sq).d j (j + 1) = d j := CochainComplex.of_d _ _ _
    rw [hd]
    exact hD j U x

end LateralTheory.KummerTheory.LHCut
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.CorepPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.LHCut

theorem corep_of : Corep := by
  intro Λ _ S U
  let M : ModuleCat.{1} (ULift.{1} Λ) := ModuleCat.of (ULift.{1} Λ) (ULift.{1} Λ)
  let P : SlShv Λ S := Sheaf.freeYoneda (Scheme.etaleTopology.over S) U M
  have key : ∀ (F : SlShv Λ S) (φ : P ⟶ F),
      Sheaf.freeYonedaHomEquiv φ = Sheaf.freeYonedaHomEquiv (𝟙 P) ≫ φ.hom.app (op U) := by
    intro F φ
    conv_lhs => rw [← Category.id_comp φ]
    simp only [Sheaf.freeYonedaHomEquiv]
    rfl
  refine ⟨P, (Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1, fun F => ?_⟩
  have e : (fun φ : P ⟶ F => (φ.hom.app (op U)).hom ((Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1)) =
      (fun g : M ⟶ F.obj.obj (op U) => g.hom 1) ∘ Sheaf.freeYonedaHomEquiv := by
    funext φ
    simp only [Function.comp_apply, key F φ]
    rfl
  rw [e]
  refine Function.Bijective.comp ⟨fun g h hgh => ?_, fun n => ?_⟩ (Equiv.bijective _)
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have : x = x • (1 : ULift.{1} Λ) := (mul_one x).symm
    rw [this, map_smul, map_smul]
    exact congrArg (x • ·) hgh
  · exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} Λ) _ n), one_smul _ n⟩

end LateralTheory.KummerTheory.LHCut
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.CupSchPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem cupSch_ev_pos {R : Type} [CommRing R] {X : Scheme.{0}} {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (hα : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U),
      ev α (p + 1) s h U y = 0) :
    ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) p U), ev α p s h U y = 0 := by
  intro p hp s h U y
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact hα q s h U y

theorem cupSch_mul_cast {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {n m k : ℤ}
    (f : ∀ s : ℤ, s = n → Sec (I.X s) U) (g : ∀ t : ℤ, t = m → Sec (J.X t) U)
    (s t : ℤ) (hs : s = n) (ht : t = m) (h : s + t = k) (hk : n + m = k) :
    μ.mul U s t k h (f s hs) (g t ht) = μ.mul U n m k hk (f n rfl) (g m rfl) := by
  subst hs; subst ht; rfl

theorem CupSch_of (hAW : CupAW) : CupSch := by
  intro R _ I J K μ X n m k hk x y a b hx hy
  obtain ⟨α, rfl, ha, hα⟩ := hx
  obtain ⟨β, rfl, hb, hβ⟩ := hy
  obtain ⟨γ, hγ, hc⟩ := hAW R μ (sch.obj X) hk α β
  refine ⟨γ, hc.symm, ?_, ?_⟩
  · have h0 := hγ 0 k (by simp) X (𝟙 X)
    rw [h0, Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rw [← ha, ← hb]
    exact cupSch_mul_cast μ X (fun s hs => ev α.1 0 s (by omega) X (𝟙 X)) (fun t ht => ev β.1 0 t (by omega) X (𝟙 X))
      _ _ (by simp) (by simp) _ hk
  · intro p s h U z
    rw [hγ (p + 1) s h U z]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) = 0
    · rw [cupSch_ev_pos β.1 hβ ((p + 1) - (i : ℕ)) (by omega), map_zero, smul_zero]
    · rw [cupSch_ev_pos α.1 hα (i : ℕ) (by omega), map_zero, LinearMap.zero_apply, smul_zero]

end LateralTheory.KummerTheory
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.LhNatPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LhNatPf

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_fst, Category.comp_id]

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_snd]

theorem pull_pull (q : ℕ) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {n i : ℤ} (x : Ht q E'' n i) :
    pull _ f _ _ (pull _ g _ _ x) = pull _ (f ≫ g) _ _ x := (pull_comp _ f g _ _ x).symm

theorem lhNat_of : LateralTheory.KummerTheory.LHCut.LhNat := by
  intro hA q _ X S p i r c M n V U g y
  unfold LateralTheory.KummerTheory.lh

  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
  unfold LateralTheory.KummerTheory.ext
  rw [pull_cast, (hA q).1, pull_pull, pull_pull, pull_pull, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, rst_fst, rst_snd]

end LateralTheory.KummerTheory.LhNatPf
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.LocalHomotopyEtaleCohomology

section

@[expose] public section

namespace LateralTheory.Fin.LH
theorem etale_kunneth_normalized_dictionary_exists_in_continuity_assembly : LateralTheory.KummerTheory.DictExist := by
  apply LateralTheory.KummerTheory.DictExist_of
theorem etale_kunneth_normalization_construction_valid_in_continuity_assembly : LateralTheory.KummerTheory.NrmMk := by
  apply LateralTheory.KummerTheory.NrmMk_of
theorem etale_kunneth_dictionary_normalized_in_continuity_assembly : LateralTheory.KummerTheory.DictNormal := by
  apply LateralTheory.KummerTheory.DictNormal_of' <;> first | exact etale_kunneth_normalization_construction_valid_in_continuity_assembly
theorem etale_kunneth_dictionary_vanishes_on_zero_in_continuity_assembly : LateralTheory.KummerTheory.DictZero := by
  apply LateralTheory.KummerTheory.DictZero_of
theorem etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly : LateralTheory.KummerTheory.Dict := by
  apply LateralTheory.KummerTheory.Dict_of' <;> first | exact etale_kunneth_normalized_dictionary_exists_in_continuity_assembly | exact etale_kunneth_dictionary_normalized_in_continuity_assembly | exact etale_kunneth_dictionary_vanishes_on_zero_in_continuity_assembly
theorem etale_cup_product_alexander_whitney_compatible_in_local_homotopy_assem : LateralTheory.KummerTheory.CupAW := by
  apply LateralTheory.KummerTheory.CupAW_of
theorem etale_cup_product_on_schemes_associative_in_local_homotopy_assembly : LateralTheory.KummerTheory.CupSch := by
  apply LateralTheory.KummerTheory.CupSch_of <;> first | exact etale_cup_product_alexander_whitney_compatible_in_local_homotopy_assem
theorem etale_ghost_cohomology_class_vanishes_in_local_homotopy_assembly : LateralTheory.KummerTheory.Ghost := by
  apply LateralTheory.KummerTheory.GhostPf.Ghost_of
theorem etale_forget_preservesInjectiveObjects : LateralTheory.KummerTheory.ForgetInj := by
  apply LateralTheory.KummerTheory.ForgetInj_of
theorem etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a : LateralTheory.KummerTheory.InjSlice := by
  apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects
theorem etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly : LateralTheory.KummerTheory.StrictHenselization := by
  apply LateralTheory.KummerTheory.SHenCut.shen
theorem etale_continuity_by_five_lemma_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Five := by
  apply LateralTheory.KummerTheory.FivePf.Five_of
theorem etale_continuity_by_induction_on_cover_size_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Ind := by
  apply LateralTheory.KummerTheory.IndPf.Ind_of
theorem etale_continuity_commutes_with_base_change_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.BC := by
  apply LateralTheory.KummerTheory.BCPf.BC_of
theorem etale_continuity_glues_along_open_covers_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Glue := by
  apply LateralTheory.KummerTheory.GluePf.Glue_of
theorem etale_flasque_sheaf_colimit_acyclic_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Flasque := by
  apply LateralTheory.KummerTheory.FlasquePf.Flasque_of
theorem etale_mayer_vietoris_connecting_map_compatible_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Delta := by
  apply LateralTheory.KummerTheory.ContCut.Delta_of <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_continuity_glues_along_open_covers_in_continuity_assembly | exact etale_flasque_sheaf_colimit_acyclic_in_continuity_assembly
theorem etale_kunneth_colimit_sequence_exact_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Exact := by
  apply LateralTheory.KummerTheory.ExactPf.Exact_of <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_continuity_glues_along_open_covers_in_continuity_assembly | exact etale_flasque_sheaf_colimit_acyclic_in_continuity_assembly
theorem etale_mayer_vietoris_sequence_natural_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.MVnat := by
  apply LateralTheory.KummerTheory.MVnatPf.MVnat_of <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_mayer_vietoris_connecting_map_compatible_in_continuity_assembly | exact etale_kunneth_colimit_sequence_exact_in_continuity_assembly
theorem etale_kunneth_continuity_for_affine_ring_colimits_in_continuity_assemb : LateralTheory.KummerTheory.ContCut.AffRing := by
  apply LateralTheory.KummerTheory.AffRingPf.AffRing_of
theorem etale_kunneth_continuity_on_affine_schemes_in_continuity_assembly : LateralTheory.KummerTheory.ContCut.Aff := by
  apply LateralTheory.KummerTheory.AffPf.Aff_of <;> first | exact etale_kunneth_continuity_for_affine_ring_colimits_in_continuity_assemb
theorem etale_kunneth_cohomology_continuous_under_limits_in_continuity_assembl : LateralTheory.KummerTheory.Cont := by
  apply LateralTheory.KummerTheory.ContCut.goal_of <;> first | exact etale_continuity_by_five_lemma_in_continuity_assembly | exact etale_continuity_by_induction_on_cover_size_in_continuity_assembly | exact etale_continuity_commutes_with_base_change_in_continuity_assembly | exact etale_continuity_glues_along_open_covers_in_continuity_assembly | exact etale_flasque_sheaf_colimit_acyclic_in_continuity_assembly | exact etale_mayer_vietoris_connecting_map_compatible_in_continuity_assembly | exact etale_kunneth_colimit_sequence_exact_in_continuity_assembly | exact etale_mayer_vietoris_sequence_natural_in_continuity_assembly | exact etale_kunneth_continuity_for_affine_ring_colimits_in_continuity_assemb | exact etale_kunneth_continuity_on_affine_schemes_in_continuity_assembly | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly
theorem etale_local_homotopy_map_on_sections_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.LhSec := by
  apply MuPairClasses.Cb.etale_lefschetz_hochschild_section_of_cup_schema_and_kummer <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_cup_product_on_schemes_associative_in_local_homotopy_assembly | exact etale_ghost_cohomology_class_vanishes_in_local_homotopy_assembly | exact etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a | exact etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly | exact etale_kunneth_cohomology_continuous_under_limits_in_continuity_assembl
theorem etale_local_homotopy_map_natural_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.LhNat := by
  apply LateralTheory.KummerTheory.LhNatPf.lhNat_of
theorem etale_mapping_cone_algebraic_description_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.ConeAlg := by
  apply LateralTheory.KummerTheory.ConeAlgPf.coneAlg_of
theorem etale_localized_kernel_vanishes_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.LocKer := by
  apply LateralTheory.KummerTheory.LHCut.locKer_of <;> first | exact etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly | exact etale_local_homotopy_map_natural_in_local_homotopy_assembly
theorem etale_cokernel_vanishes_on_affines_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.CokAff := by
  apply LateralTheory.KummerTheory.LHCut.CokAff_of <;> first | exact etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly | exact etale_kunneth_cohomology_continuous_under_limits_in_continuity_assembl | exact etale_local_homotopy_map_natural_in_local_homotopy_assembly
theorem etale_localized_cokernel_vanishes_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.LocCok := by
  apply LateralTheory.KummerTheory.LHCut.locCok_of_cokAff <;> first | exact etale_cokernel_vanishes_on_affines_in_local_homotopy_assembly | exact etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly | exact etale_kunneth_cohomology_continuous_under_limits_in_continuity_assembl | exact etale_local_homotopy_map_natural_in_local_homotopy_assembly | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_cup_product_on_schemes_associative_in_local_homotopy_assembly | exact etale_ghost_cohomology_class_vanishes_in_local_homotopy_assembly | exact etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
theorem etale_localized_mapping_cone_vanishes_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.LocCone := by
  apply LateralTheory.KummerTheory.LHCut.locCone_of <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_local_homotopy_map_on_sections_in_local_homotopy_assembly | exact etale_mapping_cone_algebraic_description_in_local_homotopy_assembly
theorem etale_extension_group_isomorphism_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.ExIso := by
  apply LateralTheory.KummerTheory.ExIsoPf.exIso_of <;> first | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_local_homotopy_map_on_sections_in_local_homotopy_assembly
theorem etale_cohomology_functor_corepresentable_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.Corep := by
  apply LateralTheory.KummerTheory.LHCut.corep_of
theorem etale_cohomology_class_killed_by_homotopy_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.HomKill := by
  apply LateralTheory.KummerTheory.HomKillPf.homKill_of
theorem etale_mapping_cone_object_acyclic_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.ConeObj := by
  apply LateralTheory.KummerTheory.LHCut.coneObj_of <;> first | exact etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
theorem etale_mapping_cone_complex_acyclic_in_local_homotopy_assembly : LateralTheory.KummerTheory.LHCut.ConeCx := by
  apply LateralTheory.KummerTheory.LHCut.coneCx_of <;> first | exact etale_mapping_cone_object_acyclic_in_local_homotopy_assembly | exact etale_mapping_cone_algebraic_description_in_local_homotopy_assembly
theorem etale_local_homotopy_cohomology_isomorphism_in_local_homotopy_assembly : LateralTheory.KummerTheory.LH := by
  apply LateralTheory.KummerTheory.LHCut.lh_of <;> first | exact etale_local_homotopy_map_on_sections_in_local_homotopy_assembly | exact etale_local_homotopy_map_natural_in_local_homotopy_assembly | exact etale_mapping_cone_algebraic_description_in_local_homotopy_assembly | exact etale_localized_kernel_vanishes_in_local_homotopy_assembly | exact etale_localized_cokernel_vanishes_in_local_homotopy_assembly | exact etale_localized_mapping_cone_vanishes_in_local_homotopy_assembly | exact etale_extension_group_isomorphism_in_local_homotopy_assembly | exact etale_cohomology_functor_corepresentable_in_local_homotopy_assembly | exact etale_cohomology_class_killed_by_homotopy_in_local_homotopy_assembly | exact etale_mapping_cone_object_acyclic_in_local_homotopy_assembly | exact etale_mapping_cone_complex_acyclic_in_local_homotopy_assembly | exact etale_kunneth_dictionary_exists_for_sheaves_in_continuity_assembly | exact etale_cup_product_on_schemes_associative_in_local_homotopy_assembly | exact etale_ghost_cohomology_class_vanishes_in_local_homotopy_assembly | exact etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a | exact etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly | exact etale_kunneth_cohomology_continuous_under_limits_in_continuity_assembl
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.LH := etale_local_homotopy_cohomology_isomorphism_in_local_homotopy_assembly
end LateralTheory.Fin.LH
end
end
