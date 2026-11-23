module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureNormalModelUnitaryModuliPoinStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrimeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpens

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinCover

theorem exists_finite_union {X : Scheme.{0}} {T : Type} (N : T → Scheme.{0}) (p : ∀ t, N t ⟶ X)
    (hp : ∀ t, IsFinite (p t)) (S : Finset T) :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ (∀ t ∈ S, Set.range (p t) ⊆ Set.range q) ∧
      ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (z : Sp K ⟶ N t), z ≫ p t = y' ≫ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨∅, Scheme.emptyTo X, inferInstance, by simp, fun K _ y' => ?_⟩
    exact (show PEmpty from y' (closedPoint K)).elim
  | insert a S _ ih =>
    obtain ⟨Y, q, hq, hr, hK⟩ := ih
    have := hp a
    refine ⟨N a ⨿ Y, coprod.desc (p a) q, inferInstance, fun t ht => ?_, fun K _ y' => ?_⟩
    · rintro _ ⟨x, rfl⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨(coprod.inl : N t ⟶ N t ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
      · obtain ⟨y, hy⟩ := hr t ht ⟨x, rfl⟩
        exact ⟨(coprod.inr : Y ⟶ N a ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc, hy]⟩
    · have hsub : ∀ x : Sp K, x = closedPoint K := fun x =>
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      have hc := (isCompl_range_inl_inr (N a) Y).sup_eq_top
      have hm : y' (closedPoint K) ∈ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) ∪
          Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
        have h : y' (closedPoint K) ∈ (⊤ : Set (N a ⨿ Y : Scheme.{0})) := trivial
        rw [← hc] at h
        exact h
      rcases hm with hm | hm
      · have hs : Set.range y' ⊆ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        refine ⟨a, IsOpenImmersion.lift _ y' hs, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inl_desc]
      · have hs : Set.range y' ⊆ Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        obtain ⟨t, z, hz⟩ := hK K (IsOpenImmersion.lift _ y' hs)
        refine ⟨t, z, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inr_desc, hz]

theorem exists_finite_surjective_cover : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  intro X Z i T _ M U g hg hU hx
  have hU' : ∀ t, Set.range i ⊆ Set.range (U t).ι := fun t => by
    rw [Scheme.Opens.range_ι]; exact hU t
  have := Fintype.ofFinite T
  let i' : ∀ t, X ⟶ (U t).toScheme := fun t => IsOpenImmersion.lift (U t).ι i (hU' t)
  have hi' : ∀ t, i' t ≫ (U t).ι = i := fun t => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨Y, q, hq, hr, hK⟩ := exists_finite_union (fun t => pullback (g t) (i' t))
    (fun t => pullback.snd (g t) (i' t)) (fun t => by have := hg t; infer_instance) Finset.univ
  refine ⟨Y, q, hq, ⟨fun x => ?_⟩, fun K _ y' => ?_⟩
  · obtain ⟨t, w, hw⟩ := hx x
    have := hg t
    refine hr t (Finset.mem_univ t) ?_
    rw [Scheme.Pullback.range_snd]
    rw [← hi' t, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      (U t).ι.isOpenEmbedding.isInducing.specializes_iff] at hw
    exact hw.mem_closed (g t).isClosedMap.isClosed_range ⟨w, rfl⟩
  · obtain ⟨t, z, hz⟩ := hK K y'
    refine ⟨t, z ≫ pullback.fst (g t) (i' t), ?_⟩
    rw [Category.assoc, pullback.condition_assoc, hi' t, ← Category.assoc, hz, Category.assoc]

end GlobalTheory.FinCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpensStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_surjective_cover_from_opens : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  first | exact @GlobalTheory.FinCover.exists_finite_surjective_cover | exact GlobalTheory.FinCover.exists_finite_surjective_cover | (intros; apply GlobalTheory.FinCover.exists_finite_surjective_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XScov

theorem genericPoints_XF_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, he⟩ := Xo.qproj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (KA l) N
  haveI : QuasiCompact Xo.s := he ▸ inferInstance
  haveI : LocallyOfFiniteType Xo.s := he ▸ inferInstance
  haveI : QuasiCompact (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : CompactSpace (Xo.XF c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : IsNoetherian (Xo.XF c) := {}
  exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian

end GlobalTheory.XScov
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  first | exact @GlobalTheory.XScov.genericPoints_XF_finite | exact GlobalTheory.XScov.genericPoints_XF_finite | (intros; apply GlobalTheory.XScov.genericPoints_XF_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

theorem uAct_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  intro E _ _ _ H Dw l Xo c o Ω _ _ _ R R' h P P' φ hφ hL act u hact hU

  have inj : ∀ {T : Over (Sp R')} {x y : T ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let act' : 𝓞 E → (P'.A ⟶ P'.A) := fun a => Over.homMk (hφ.1.lift (φ ≫ (act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hφ.1.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R')} (x : T ⟶ P'.A) a, pushPt hφ.1.w (x ≫ act' a) = pushPt hφ.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have hact' : ∀ a, IsMonHom (act' a) := fun a => isMonHom_of_mul _ fun T x y => inj (by
    have := hact a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  refine ⟨act', hact', ha, ?_⟩

  obtain ⟨G, _, α, β, hα, hβ, hLG, hf⟩ := hU
  set g := (Subalgebra.inclusion (ratHull_mono h)).toRingHom with hg
  have hG := isGrpPullback_pullback G (spMap g)
  have e : spMap g ≫ spMap (toRat R) = spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hα₀ : IsGrpPullback ((Over.pullback (spMap g)).obj G) P.A
      (spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom) (pullback.fst _ _ ≫ α) := (hG.comp hα).congr e rfl
  have w : (pullback.fst G.hom (spMap g) ≫ α) ≫ P.A.hom =
      (((Over.pullback (spMap g)).obj G).hom ≫ spMap (toRat R')) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [Category.assoc]; exact hα₀.1.w
  have e₁ := hφ.1.lift_fst _ _ w
  have hα' := hφ.cancel (hα₀.congr rfl e₁.symm) (hφ.1.lift_snd _ _ w)
  have hβ' := (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl
  refine ⟨_, _, hφ.1.lift _ _ w, pullback.fst _ _ ≫ β, hα', hβ', ?_, fun a => ?_⟩
  · exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
      (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) (GenSpread.lbIso_pull_comp _ rfl rfl hLG)
  · obtain ⟨f, hfα, hfβ⟩ := hf a
    have hfl : ((Over.pullback (spMap g)).map f).left ≫ pullback.fst G.hom (spMap g) = pullback.fst G.hom (spMap g) ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (spMap g)).map f, ?_, ?_⟩
    · apply hφ.1.hom_ext
      · rw [Category.assoc, e₁, Category.assoc, ha, ← Category.assoc (hφ.1.lift _ _ w), e₁,
          ← Category.assoc _ (pullback.fst _ _), hfl, Category.assoc, hfα, Category.assoc]
      · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, Over.w, hφ.1.lift_snd, ← Category.assoc, Over.w]
    · rw [← Category.assoc, hfl, Category.assoc, hfβ, Category.assoc]

end GlobalTheory.UCovSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryAction_baseChange_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  first | exact @GlobalTheory.UCovSep.uAct_baseChange | exact GlobalTheory.UCovSep.uAct_baseChange | (intros; apply GlobalTheory.UCovSep.uAct_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystems

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory.UCovSep

namespace GlobalTheory.UCovSep



theorem exists_linked_cov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw hpq l Xo c C n hn ho j₀
  classical
  haveI : Finite (genericPoints (Xo.XF c)) := (GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField E H Dw l Xo c).to_subtype
  letI : Fintype (genericPoints (Xo.XF c)) := Fintype.ofFinite _
  choose g₀ hA using fun τ : genericPoints (Xo.XF c) => GlobalTheory.T.exists_levelStructure_normalModel_unitaryModuliPoint E H Dw hpq l Xo c C τ.1 n hn ho
  choose k j₁ hk _hB hj₁ big using fun τ : genericPoints (Xo.XF c) =>
    GlobalTheory.UPoinc.GSetup.exists_big_level (g₀ τ) n hn.two_le 0
  set J := j₀ + ∑ τ, (k τ + j₁ τ) + 1 with hJ
  have hkJ : ∀ τ, k τ + j₁ τ + j₀ + 1 ≤ J := fun τ => by
    have := Finset.single_le_sum (f := fun τ => k τ + j₁ τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  choose o₁ Ω i₁ i₂ i₃ i₄ ze uτ A₁ lev M U g hAg hun hx hUO hpt hMn hMp hgf hrange using fun τ => hA τ (4 * J)
  obtain ⟨Y, q, hqf, hqs, hY⟩ := GlobalTheory.T.exists_finite_surjective_cover_from_opens (Xo.XF c) C.Z C.i (genericPoints (Xo.XF c)) (fun τ => (M τ).Z) U g hgf
    (fun τ => by
      rintro _ ⟨x, rfl⟩
      exact hrange τ ⟨C.iF x, rfl⟩)
    (fun x => by
      obtain ⟨τ, hτ, hsp⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
      refine ⟨⟨τ, hτ⟩, (M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩)), ?_⟩
      have h₁ : (g ⟨τ, hτ⟩ ≫ (U ⟨τ, hτ⟩).ι) ((M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩))) = C.i τ := by
        refine (congrArg (fun χ : Sp (Ω ⟨τ, hτ⟩) ⟶ C.Z => χ (closedPoint (Ω ⟨τ, hτ⟩))) (hpt ⟨τ, hτ⟩)).trans ?_
        exact congrArg C.i (hx ⟨τ, hτ⟩ (closedPoint (Ω ⟨τ, hτ⟩)))
      rw [h₁]
      exact hsp.map C.i.continuous)
  refine ⟨J, Y, q, by omega, hqf, hqs, fun K _ y' => ?_⟩
  obtain ⟨t, yM, hyM⟩ := hY K y'
  letI := i₁ t
  letI := i₂ t
  letI := i₃ t
  haveI := i₄ t
  obtain ⟨R, P, act, u, 𝔭, hRfg, hfr, hPg, hS, ⟨levR⟩, hact, hUA, hu, h𝔭, hreg𝔭⟩ :=
    GlobalTheory.T.exists_local_spread_universal_abelian_scheme E H Dw hpq l Xo c C (o₁ t) (Ω t) (M t) (g t ≫ (U t).ι) (uτ t) (hMn t) (hpt t)
      (A₁ t) (n ^ (4 * J)) (ze t) (by rw [Nat.cast_pow]; exact (hun t).pow _) (hUO t) (lev t) K yM (y' ≫ q)
      (by rw [Category.assoc]; simpa only [Category.assoc] using hyM)
  have e : (n ^ (2 * J - 2 * k t) * (n ^ k t) ^ 2) ^ 2 = n ^ (4 * J) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  obtain ⟨S, ρ, hR, φ, hreg, -, hN, hr, hgS, hpb, hL, -⟩ := GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime (o₁ t) (Ω t) R hRfg hfr 𝔭 h𝔭 P n (k t)
    (2 * J - 2 * k t) (ze t) hn ho (hk t) (by have := hkJ t; omega) (hun t) hS (e ▸ levR)
  obtain ⟨act', hact', -, hUA'⟩ := GlobalTheory.T.unitaryAction_baseChange_subalgebra E H Dw l Xo c (o₁ t) (Ω t) R S.R hR P ρ.P φ hpb hL act u hact hUA
  have hu' : spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u = uτ t := by
    rw [← hu, ← Category.assoc, ← Spec.map_comp]; rfl
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) w ∈
      genericPoints (Xo.XF c) := fun w => by rw [hu', hx t w]; exact t.2
  have hptS : (M t).pt ≫ (g t ≫ (U t).ι) =
      spMap (ratHull S.R).val.toRingHom ≫ (spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) ≫ C.i := by
    rw [hpt t, ← hu', Category.assoc]
  have hbig : S.Big := big t _ (by have := hkJ t; omega) (o₁ t) (Ω t) S (hgS.trans (hPg.trans (hAg t))) hN hr
  let X₁ : GlobalTheory.GSep.GSet :=
    { o₁ := o₁ t, Ω₁ := Ω t, S := S, ρ := ρ, big := hbig, M := M t, normal := hMn t, projM := hMp t,
      div := C.thetaInt (o₁ t) (Ω t) S ρ _ hUA'.uOver hgen (M t) (g t ≫ (U t).ι)
        (hMn t) hptS }
  refine ⟨X₁, act', spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u, g t ≫ (U t).ι, yM,
    ⟨hact', hUA', hgen, hptS⟩, ?_, ⟨U t, g t, hgf t, rfl, hrange t⟩, by simpa only [Category.assoc] using hyM, ?_⟩
  · show S.r * S.N = _
    rw [hr, hN, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  · intro a ha
    obtain ⟨a', b', hb', rfl⟩ := hreg a ha
    exact hreg𝔭 a' b' hb'

end GlobalTheory.UCovSep
end
end
