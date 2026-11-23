module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocalStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpenStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    (letI := (ρ.restrict S S' hρ).toAlgebra
     IsLocalization.Away (⟨s, hs⟩ : S) S') := by
  let := ρ.toAlgebra
  let := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα U f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  first | exact @GlobalTheory.QcSub.coequifibered_subNat | exact GlobalTheory.QcSub.coequifibered_subNat | (intros; apply GlobalTheory.QcSub.coequifibered_subNat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  first | exact @GlobalTheory.sub_choose_finite | exact GlobalTheory.sub_choose_finite | (intros; apply GlobalTheory.sub_choose_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem exists_finite_coequifibered_subalgebra : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  intro X hX F α hα hint n U S
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun A : X.AffineZariskiSite => (A.1 : Set X)) (fun A => A.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  let V : Fin n ⊕ t → X.Opens := Sum.elim (fun k => (U k).1) (fun A => A.1.1)
  have hV : ∀ j, IsAffineOpen (V j) := by
    rintro (k | A)
    exacts [(U k).2, A.1.2]
  have hcov : ∀ x : X, ∃ j, x ∈ V j := by
    intro x
    obtain ⟨A, hA, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨.inr ⟨A, hA⟩, hx⟩
  let S' : ∀ j, Set (F.obj (op (V j))) := fun j =>
    Sum.rec (motive := fun j => Set (F.obj (op (V j)))) (fun k => ((S k : Set (F.obj (op (U k).1))))) (fun _ => ∅) j
  have hS' : ∀ j, (S' j).Finite := by
    rintro (k | A)
    exacts [(S k).finite_toSet, Set.finite_empty]
  obtain ⟨T, hTfin, hST⟩ := GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover X hX F α hα V hV S' hS'
  refine ⟨subFunctor F α V T, subNat F α V T, subIncl F α V T,
    GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent X F α hα V T (GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen X hX F α hα V hV T), subNat_comp_subIncl F α V T,
    subIncl_injective F α V T,
    fun W => GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent X hX F α hα hint V hV hcov T hTfin W.unop.1 W.unop.2,
    fun k x hx => ⟨⟨x, hST (.inl k) (Finset.mem_coe.mpr hx)⟩, rfl⟩⟩

end GlobalTheory.QcSub
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  first | exact @GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | exact GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra | (intros; apply GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra <;> assumption)
end
end
