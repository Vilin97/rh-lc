module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClasses
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCompHomComplexAssocOnCohomologyClassesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  first | (exact @GlobalTheory.cocycle_comp_assoc_classes) | (exact GlobalTheory.cocycle_comp_assoc_classes) | (intros; apply GlobalTheory.cocycle_comp_assoc_classes  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZe

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeConn


set_option backward.isDefEq.respectTransparency false in
theorem cone_connecting_class : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  intro R _ S hc φ ψ hφ hψ w hw
  let Φ : Cochain (sgl S.X₂) (res R S.X₁) 0 := Cochain.fromSingleMk φ (zero_add 0)
  have hw1 : w.1 = Cochain.fromSingleMk ψ (zero_add 1) := by
    obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective w.1 1 (zero_add 1)
    rw [← hf]; congr 1
    rw [← hw, ← hf, Cochain.fromSingleMk_v]; exact (Iso.inv_hom_id_assoc _ _).symm
  have h1 : δ 0 1 Φ = (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g).comp w.1 (zero_add 1) := by
    rw [hw1, Cochain.δ_fromSingleMk φ (zero_add 0) 1 1 (zero_add 1), ← hψ]
    exact Cochain.fromSingleMk_precomp S.g ψ (zero_add 1)
  have h2 : (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0) =
      Cochain.ofHom (resAug S.X₁) := by
    refine (Cochain.fromSingleMk_precomp S.f φ (zero_add 0)).symm.trans ?_
    rw [hφ]
    apply (Cochain.fromSingleEquiv (X := S.X₁) (K := res R S.X₁) (p := 0) (zero_add 0)).injective
    rw [Cochain.fromSingleEquiv_fromSingleMk]
    change resι R S.X₁ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).inv ≫ (Cochain.ofHom (resAug S.X₁)).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]; rfl
  have h3 : Cochain.ofHom (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) =
      (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp
        (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g) (zero_add 0) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain]
    simp
  have h4 : (Cochain.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc)).comp
      (mappingCone.fst (resMap R S.f)).1 (zero_add 1) =
      (mappingCone.fst (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).1.comp
        (Cochain.ofHom (resAug S.X₁)) (add_zero 1) := by
    simp [mappingCone.map, mappingCone.ofHom_desc, mappingCone.descCochain, Cochain.add_comp]
  symm
  refine sub_eq_zero.1 ((CohomologyClass.mk_sub _ _).symm.trans ?_)
  refine (CohomologyClass.mk_eq_zero_iff _).2 ((mem_coboundaries_iff _ 0 (zero_add 1)).2
    ⟨(mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0), ?_⟩)
  have e1 := δ_zero_cochain_comp (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) Φ 1 (zero_add 1)
  rw [h1, mappingCone.δ_snd, Int.negOnePow_zero, one_smul, Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, h2,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h3, ← h4] at e1
  refine e1.trans ?_
  simp [zcomp, sub_eq_add_neg]

end GlobalTheory.EtC.ConeConn
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZeStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  first | (exact @GlobalTheory.EtC.ConeConn.cone_connecting_class) | (exact GlobalTheory.EtC.ConeConn.cone_connecting_class) | (intros; apply GlobalTheory.EtC.ConeConn.cone_connecting_class  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquivStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLes

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LesChar

variable {R' : Type} [CommRing R']

theorem resAug_comm (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

theorem mk_ofHom_eq {K L : Cx R'} {f g : K ⟶ L} (ho : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨-1, by omega, Cochain.ofHomotopy ho, by ext; simp [δ_ofHomotopy]⟩

theorem exact_part : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) → ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n)
      (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl)
      (HK.post R K S.f (n + 1)) := by
  intro R _ S e h K n
  obtain ⟨hid, -, hcomp, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  obtain ⟨-, -, hass⟩ := GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes R (add_zero n) (zero_add 1) (rfl : n + 1 = n + 1) (rfl : n + 1 = n + 1)
  obtain ⟨x1, x2, x3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K (resMap R S.f) n
  have hg : ∀ x, HK.post R K S.g n x = cpush K e.hom n (cpush K (mappingCone.inr (resMap R S.f)) n x) := by
    intro x
    rw [← hcomp]
    exact (congrFun (congrArg DFunLike.coe ((hhtp _ _ ⟨h⟩ K n).2)) x).symm
  have hz : ∀ x, HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl x =
      cpost K (mappingCone.fst (resMap R S.f)) n (n + 1) rfl (cpush K e.inv n x) := fun x => hass _ _ _
  have hie : ∀ x, cpush K e.inv n (cpush K e.hom n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyHomInvId⟩ K n).2]
    exact (hid K _ n x).2
  have hei : ∀ x, cpush K e.hom n (cpush K e.inv n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyInvHomId⟩ K n).2]
    exact (hid K _ n x).2
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [hg, ← map_zero (cpush K e.hom n)]
    constructor
    · intro hy
      exact (x1 _).1 (by rw [← hie (cpush K (mappingCone.inr (resMap R S.f)) n y), hy, hie])
    · intro hy
      rw [(x1 _).2 hy]
  · rw [hz]
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x2 _).1 hy
      exact ⟨x, by rw [hg, hx, hei]⟩
    · rintro ⟨x, rfl⟩
      rw [hg, hie]
      exact (x2 _).2 ⟨x, rfl⟩
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x3 _).1 hy
      exact ⟨cpush K e.hom n x, by rw [hz, hie, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [hz]
      exact (x3 _).2 ⟨_, rfl⟩

theorem zcomp_ofHom_ofHom {K L M N : Cx R'} {n : ℤ} (f : K ⟶ L) (g : L ⟶ M) (b : Cocycle M N n) :
    zcomp (Cocycle.ofHom f) (zcomp (Cocycle.ofHom g) b (zero_add n)) (zero_add n) =
      zcomp (Cocycle.ofHom (f ≫ g)) b (zero_add n) := by
  ext1
  change (Cochain.ofHom f).comp ((Cochain.ofHom g).comp b.1 (zero_add n)) (zero_add n) =
    (Cochain.ofHom (f ≫ g)).comp b.1 (zero_add n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem assemble {D C I₃ I₁ X : Cx R'} (q : D ⟶ X) (a : X ⟶ I₃) (m : D ⟶ C) (eh : C ⟶ I₃) (ei : I₃ ⟶ C)
    (fst : Cocycle C I₁ 1) (w : Cocycle X I₁ 1) (hh : Homotopy (eh ≫ ei) (𝟙 C))
    (cmp : CohomologyClass.mk (Cocycle.ofHom (q ≫ a)) = CohomologyClass.mk (Cocycle.ofHom (m ≫ eh)))
    (key : CohomologyClass.mk (zcomp (Cocycle.ofHom m) fst (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))) :
    cpull q I₁ 1 (CohomologyClass.mk (zcomp (Cocycle.ofHom a) (zcomp (Cocycle.ofHom ei) fst (zero_add 1)) (zero_add 1))) =
      cpull q I₁ 1 (CohomologyClass.mk w) := by
  have h1 : CohomologyClass.mk (Cocycle.ofHom ((m ≫ eh) ≫ ei)) = CohomologyClass.mk (Cocycle.ofHom m) :=
    mk_ofHom_eq (((Homotopy.ofEq (Category.assoc _ _ _)).trans (hh.compLeft m)).trans
      (Homotopy.ofEq (Category.comp_id m)))
  change CohomologyClass.mk (zcomp (Cocycle.ofHom q) _ (zero_add 1)) = CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))
  rw [zcomp_ofHom_ofHom, ← key, ← cpost_mk, cmp, cpost_mk, zcomp_ofHom_ofHom, ← cpost_mk, h1, cpost_mk]

theorem exists_connecting_cocycle : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  intro R _ S hS
  obtain ⟨e, ⟨h⟩⟩ := GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv R S hS
  refine ⟨_, exact_part R S e h, 1, ?_⟩
  intro φ ψ hφ hψ w hw
  rw [one_smul]
  have hc := resAug_comm R S.f
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₁).IsKInjective := by unfold res; infer_instance
  apply (GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))
    (res R S.X₁) 1).1
  exact assemble _ _ _ _ _ _ _ e.homotopyHomInvId (GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq R S hS hc e h) (GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero R S hc φ ψ hφ hψ w hw)

end GlobalTheory.EtC.LesChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  first | (exact @GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (exact GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (intros; apply GlobalTheory.EtC.LesChar.exists_connecting_cocycle  <;> assumption)
end
end
