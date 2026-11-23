module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelObjIsoHomSubtype
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySectionsStatement
public import Mathlib.Order.CompletePartialOrder
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
open Scheme.AffineZariskiSite

noncomputable section

theorem exists_finite_of_isFinSub : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first
  | exact @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | (apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover ..)

end

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finite_normalization_integral_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first | exact @GlobalTheory.Mum.exists_finite_of_isFinSub | exact GlobalTheory.Mum.exists_finite_of_isFinSub | (intros; apply GlobalTheory.Mum.exists_finite_of_isFinSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem resK_bijective {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V)
    (e : gp ⁻¹ᵁ V ≤ gp ⁻¹ᵁ W) : Function.Bijective (resK gp h) := by
  have e' : gp ⁻¹ᵁ W = gp ⁻¹ᵁ V := le_antisymm (gp.preimage_mono h) e
  have hh : homOfLE (gp.preimage_mono h) = eqToHom e' := Subsingleton.elim _ _
  show Function.Bijective ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom
  rw [hh]
  exact ConcreteCategory.bijective_of_isIso ((Sp K).presheaf.map (eqToHom e').op)

theorem isIntegralElem_of_comp_injective {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Injective g) {y : A}
    (h : (g.comp f).IsIntegralElem (g y)) : f.IsIntegralElem y := by
  obtain ⟨p, hp, hy⟩ := h
  refine ⟨p, hp, hg ?_⟩
  rw [Polynomial.hom_eval₂, hy, map_zero]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_bot_or_eq_top_of_sp (K : Type) [Field K] (O : (Sp K).Opens) : O = ⊥ ∨ O = ⊤ := by
  by_cases h : O = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp h
    refine top_unique fun z _ => ?_
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim z x]
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_closure_of_isIntegralElem_affine_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  intro S K _ gp V W hWV hV hW b hb
  classical
  let C : Finset Γ(Sp K, gp ⁻¹ᵁ V) → Subring Γ(Sp K, gp ⁻¹ᵁ W) := fun s =>
    Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _))
  have Cmono : ∀ s t : Finset Γ(Sp K, gp ⁻¹ᵁ V), s ⊆ t → C s ≤ C t := by
    intro s t hst
    refine Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono ?_))
    exact_mod_cast hst
  let J : Ideal Γ(S, W) :=
    { carrier := {c | ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
        (gp.app W).hom c * b ∈ C s}
      zero_mem' := ⟨∅, by simp, by rw [map_zero, zero_mul]; exact zero_mem _⟩
      add_mem' := by
        rintro c d ⟨s, hs, hc⟩ ⟨t, ht, hd⟩
        refine ⟨s ∪ t, fun y hy => (Finset.mem_union.mp hy).elim (hs y) (ht y), ?_⟩
        rw [map_add (f := _), add_mul]
        exact add_mem (Cmono _ _ Finset.subset_union_left hc) (Cmono _ _ Finset.subset_union_right hd)
      smul_mem' := by
        rintro c d ⟨s, hs, hd⟩
        refine ⟨s, hs, ?_⟩
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hd }
  let T : Set Γ(S, W) := {c | ∃ g : Γ(S, V), S.basicOpen g ≤ W ∧ (S.presheaf.map (homOfLE hWV).op).hom g = c}
  have hspan : Ideal.span T = ⊤ := by
    refine hW.self_le_iSup_basicOpen_iff.mp ?_
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWV hx)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨_, g, hg, rfl⟩, ?_⟩
    show x ∈ S.basicOpen ((S.presheaf.map (homOfLE hWV).op).hom g)
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hxg⟩
  have hT : T ⊆ J.radical := by
    rintro _ ⟨g, hg, rfl⟩
    set D := S.basicOpen g with hD
    rcases eq_bot_or_eq_top_of_sp K (gp ⁻¹ᵁ D) with h0 | h1
    ·
      have hz : (gp.app V).hom g = 0 := by
        rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
        exact h0
      refine ⟨1, ∅, by simp, ?_⟩
      rw [pow_one, ← resK_app, hz, map_zero, zero_mul]
      exact zero_mem _
    ·
      have hDW : D ≤ W := hg
      have hDV : D ≤ V := hDW.trans hWV
      have := hV.isLocalization_basicOpen g
      letI : Algebra Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := (gp.app D).hom.toAlgebra
      letI : Algebra Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := ((gp.app D).hom.comp (algebraMap Γ(S, V) Γ(S, D))).toAlgebra
      haveI : IsScalarTower Γ(S, V) Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have sq : (resK gp hDW).comp (gp.app W).hom =
          (gp.app D).hom.comp (S.presheaf.map (homOfLE hDW).op).hom := by
        ext a; exact resK_app gp hDW a
      have hb' : IsIntegral Γ(S, D) (resK gp hDW b) := by
        have := hb.map (resK gp hDW)
        rw [sq] at this
        exact RingHom.isIntegralElem.of_comp _ _ this
      obtain ⟨⟨_, N, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g)
        (Rₘ := Γ(S, D)) _ hb'
      have top : ∀ U : S.Opens, gp ⁻¹ᵁ U ≤ gp ⁻¹ᵁ D := fun _ => h1 ▸ le_top
      obtain ⟨y, hy⟩ := (resK_bijective gp hDV (top V)).2 ((g ^ N) • resK gp hDW b)
      have alg : ∀ a : Γ(S, V), algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) a = resK gp hDV ((gp.app V).hom a) := by
        intro a; rw [resK_app]; rfl
      have hyi : (gp.app V).hom.IsIntegralElem y := by
        refine isIntegralElem_of_comp_injective _ (resK gp hDV) (resK_bijective gp hDV (top V)).1 ?_
        have e : (resK gp hDV).comp (gp.app V).hom = algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := by
          ext a; exact (alg a).symm
        rw [e, hy]
        exact hm
      refine ⟨N, {y}, by simpa using hyi, ?_⟩
      have key : resK gp hWV y = (gp.app W).hom ((S.presheaf.map (homOfLE hWV).op).hom g ^ N) * b := by
        apply (resK_bijective gp hDW (top W)).1
        rw [resK_resK, hy, Algebra.smul_def, alg, map_mul]
        simp only [map_pow]
        rw [← resK_app gp hWV g, resK_resK]
      rw [← key]
      exact Subring.subset_closure (Or.inr ⟨y, by simp, rfl⟩)
  have hJ : J = ⊤ := Ideal.radical_eq_top.mp (top_unique (hspan ▸ Ideal.span_le.mpr hT))
  obtain ⟨s, hs, h⟩ : (1 : Γ(S, W)) ∈ J := hJ ▸ Submodule.mem_top
  refine ⟨s, hs, ?_⟩
  simpa using h

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  first | exact @GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | exact GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | (intros; apply GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegular

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finSub_of_isIntegralElem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens)
    (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) →
    (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) →
    ∃ F : ∀ V : M.S.Opens, Subring Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ V), IsFinSub M.gp F ∧ ∀ m, b m ∈ F (U m) := by
  classical
  intro R _ _ _ M n U b hU hb
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : M.S.IsSeparated := ⟨by rw [← terminal.comp_from M.π]; infer_instance⟩

  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : M.S.affineOpens => (V.1 : Set M.S))
    (fun V => V.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := M.S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  let r := s.card
  let Vc : Fin r → M.S.Opens := fun i => (s.equivFin.symm i).1.1
  have hVa : ∀ i, IsAffineOpen (Vc i) := fun i => (s.equivFin.symm i).1.2
  have hcov : (⨆ i, Vc i) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨s.equivFin ⟨V, hV⟩, by simpa [Vc] using hx⟩
  have hloc : ∀ (i : Fin r) (m : Fin n), ∃ t : Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i),
      (∀ y ∈ t, (M.gp.app (Vc i)).hom.IsIntegralElem y) ∧
      resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m) (b m) ∈ Subring.closure (Set.range (M.gp.app (U m ⊓ Vc i)).hom ∪
        resK M.gp (inf_le_right : U m ⊓ Vc i ≤ Vc i) '' (t : Set _)) := by
    intro i m
    refine GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le M.gp (Vc i) (U m ⊓ Vc i) inf_le_right (hVa i) ((hU m).inf (hVa i)) _ ?_
    obtain ⟨p, hp, hpe⟩ := hb m
    refine ⟨p.map (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (M.gp.app (U m ⊓ Vc i)).hom.comp (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom =
        (resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m)).comp (M.gp.app (U m)).hom := by
      ext a; exact (resK_app M.gp _ a).symm
    rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero]
  choose t ht hbt using hloc
  let T : ∀ i, Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i) := fun i => Finset.univ.biUnion (t i)
  refine ⟨finFam M.gp Vc T, ⟨fun V _ a => finFam_range _ _ _ _ a, fun V V' hle _ _ x hx => finFam_res _ _ _ V V' hle x hx,
    fun V hV f x hx => GlobalTheory.T.finiteGeneratedSubring_localised_basicOpen M.gp Vc T V hV f x hx, fun V hV => GlobalTheory.T.finite_generation_integral_family_sections M.gp Vc T hcov ?_ V hV⟩, ?_⟩
  · intro i y hy
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 (show y ∈ Finset.univ.biUnion (t i) from hy)
    exact ht i m y hm
  · intro m
    rw [mem_finFam]
    intro i
    refine Subring.closure_mono ?_ (hbt i m)
    rintro _ (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, show z ∈ Finset.univ.biUnion (t i) from Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hz⟩, rfl⟩

theorem finiteModif_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  intro R _ _ _ M n U b hU hb
  obtain ⟨F, hF, hbF⟩ := exists_finSub_of_isIntegralElem R M n U b hU hb
  haveI : IsIntegral M.S := M.integral
  haveI : IsDominant M.gp := M.dominant
  obtain ⟨S', h, gp', hgp, hfin, hint, hdom, hsec⟩ := GlobalTheory.T.exists_finite_normalization_integral_sections M.gp F hF
  haveI := M.proper
  let M' : Modif R :=
    { S := S', π := h ≫ M.π, proper := inferInstance, integral := hint, gp := gp',
      gp_π := by rw [← Category.assoc, hgp, M.gp_π], dominant := hdom }
  exact ⟨M', h, hgp, hfin, rfl, fun m => hsec (U m) (hU m) (b m) (hbF m)⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegularStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finiteModification_integral_elements_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  first | exact @GlobalTheory.Mum.finiteModif_regular | exact GlobalTheory.Mum.finiteModif_regular | (intros; apply GlobalTheory.Mum.finiteModif_regular <;> assumption)
end
end
