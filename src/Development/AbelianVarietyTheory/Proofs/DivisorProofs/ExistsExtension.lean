module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Mathlib.RingTheory.PicardGroup
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
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ s : S, Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆ Set.range j := by
  first | exact @GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | exact GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | (intros; apply GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E] (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f → ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  first | exact @GlobalTheory.Desc.semiAbelian_hom_extend_generic | exact GlobalTheory.Desc.semiAbelian_hom_extend_generic | (intros; apply GlobalTheory.Desc.semiAbelian_hom_extend_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.StalkExt

theorem exists_agree_of_generic {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    (hf : IsMonHom f) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (t : Sp R ⟶ S) [Mono t] (k : Sp (FractionRing R) ⟶ U) (hk : k ≫ j = Out.jK R ≫ t) :
    ∃ g : pullback G.hom t ⟶ H.left, g ≫ H.hom = pullback.fst G.hom t ≫ G.hom ∧
      GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)

  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) k).comp (isGrpPullback_pullback G j)).congr hk rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj H) k).comp (isGrpPullback_pullback H j)).congr hk rfl)
  haveI := ha; haveI := hb; haveI := hf
  have hfK : IsMonHom (a.hom ≫ (Over.pullback k).map f ≫ b.inv) := inferInstance
  have hρ : (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ pullback.fst G.hom j =
      pullback.fst G.hom (Out.jK R ≫ t) := (Category.assoc _ _ _).trans ha'
  have hb2 : b.inv.left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      pullback.fst ((Over.pullback j).obj H).hom k ≫ pullback.fst H.hom j := by
    rw [← hb', ← Category.assoc, ← Over.comp_left, b.inv_hom_id, Over.id_left, Category.id_comp]
  have hK : (a.hom ≫ (Over.pullback k).map f ≫ b.inv).left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ f.left ≫ pullback.fst H.hom j := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb2, ← Category.assoc (((Over.pullback k).map f).left),
      GlobalTheory.ExtUnique.pullback_map_left_fst, Category.assoc, Category.assoc]

  obtain ⟨g, hg, hA⟩ := GlobalTheory.DedekindExt.exists_agree_of_extend (k := Out.jK R) (t := t) rfl G H
    (a.hom ≫ (Over.pullback k).map f ≫ b.inv) fun f' hf' => by
      obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre R ((Over.pullback t).obj G) ((Over.pullback t).obj H)
        (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t H hH) f' hf'
      exact ⟨F, hF⟩

  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  let c : pullback G.hom (Out.jK R ≫ t) ⟶ pullback G.hom t :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Out.jK R) (by rw [pullback.condition, Category.assoc])
  have hc₁ : c ≫ pullback.fst G.hom t = pullback.fst G.hom (Out.jK R ≫ t) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd G.hom t = pullback.snd G.hom (Out.jK R ≫ t) ≫ Out.jK R := pullback.lift_snd _ _ _
  have sq : IsPullback c (pullback.snd G.hom (Out.jK R ≫ t)) (pullback.snd G.hom t) (Out.jK R) := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback G.hom t)
    rw [hc₁]
    exact IsPullback.of_hasPullback G.hom (Out.jK R ≫ t)
  have : QuasiCompact c := MorphismProperty.of_isPullback sq.flip ‹_›
  have : IsSchemeTheoreticallyDominant c := .of_isPullback sq.flip
  refine ⟨g, hg, GlobalTheory.DedekindExt.Agree.of_dominant G.hom H.hom hf₀ hg c fun T u u' e => ?_⟩
  have h₁ := hA T (u ≫ c) u (by rw [Category.assoc, hc₁])
  have hu : u' = u ≫ a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k := by
    rw [← cancel_mono (pullback.fst G.hom j), ← e, Category.assoc, Category.assoc, hc₁, ← hρ, Category.assoc]
  rw [hu, ← Category.assoc, h₁, hK, Category.assoc, Category.assoc, Category.assoc]

theorem exists_agree_at_stalk : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  intro U S j _ G H _ _ hG hH f hf s i₁ i₂ i₃ k hk
  haveI := i₁; haveI := i₂; haveI := i₃
  exact @exists_agree_of_generic U S j _ G H _ _ hG hH f hf (S.presheaf.stalk s) _ i₁ i₂ i₃ (S.fromSpecStalk s) _ k hk

end GlobalTheory.StalkExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_at_stalk_agreeing_on_open : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  first | exact @GlobalTheory.StalkExt.exists_agree_at_stalk | exact GlobalTheory.StalkExt.exists_agree_at_stalk | (intros; apply GlobalTheory.StalkExt.exists_agree_at_stalk <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbDenseExt

theorem exists_extension : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ (A B : Over U) [GrpObj A] [GrpObj B] (φ : A.left ⟶ G.left) (ψ : B.left ⟶ H.left), IsGrpPullback A G j φ → IsGrpPullback B H j ψ → ∀ g : A ⟶ B, IsMonHom g → ∃ f : G ⟶ H, g.left ≫ ψ = φ ≫ f.left := by
  intro U S _ _ j _ hd G H _ _ hG hH A B _ _ φ ψ hA hB g hg
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB (isGrpPullback_pullback H j)
  let f := a.hom ≫ g ≫ b.hom
  have hf : IsMonHom f := by infer_instance
  have : IsDominant j := ⟨hd⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion j
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  have := hG.smooth
  have := hH.smooth
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, pullback.condition]
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.DedekindExt.exists_of_stalks (j := j) G.hom H.hom
    (IsPullback.of_hasPullback G.hom j) hf₀ fun s => by
      obtain ⟨k, hk⟩ : ∃ k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U,
          k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s :=
        ⟨IsOpenImmersion.lift j _ (GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen j hd s), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨g', hg', hA'⟩ := GlobalTheory.T.semiAbelian_hom_extends_at_stalk_agreeing_on_open j G H hG hH f hf s k hk
      exact ⟨_, S.fromSpecStalk s, 𝟙 _, g', Category.id_comp _, hg', hA'⟩
  refine ⟨Over.homMk F hF, ?_⟩
  have hφ : φ = a.inv.left ≫ pullback.fst G.hom j := by
    rw [← ha', ← Category.assoc, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]
  show g.left ≫ ψ = φ ≫ F
  rw [hφ, Category.assoc, hF']
  simp only [f, Over.comp_left, Category.assoc, hb']
  rw [← Category.assoc a.inv.left, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]

end GlobalTheory.SemiAbDenseExt
end
end
