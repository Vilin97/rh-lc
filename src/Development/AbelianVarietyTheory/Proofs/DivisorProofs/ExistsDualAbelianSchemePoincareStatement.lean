module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualRepresentableAffineBaseStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualCommStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDimStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_locally_constant_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S, ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  first | exact @GlobalTheory.DualCon.abelianScheme_locally_relDim | exact GlobalTheory.DualCon.abelianScheme_locally_relDim | (intros; apply GlobalTheory.DualCon.abelianScheme_locally_relDim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDims

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

instance isZariskiLocalAtTarget_smoothDim (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

theorem smoothDim_restrict_pullback {S T X : Scheme.{0}} (b : X ⟶ S) (t : T ⟶ S) (U : S.Opens) {n : ℕ}
    (h : SmoothOfRelativeDimension n (pullback.snd b U.ι)) :
    SmoothOfRelativeDimension n (pullback.snd b t ∣_ (t ⁻¹ᵁ U)) := by
  have big := (isPullback_morphismRestrict (pullback.snd b t) (t ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback b t)
  rw [← morphismRestrict_ι t U] at big
  have hc : ((pullback.snd b t ⁻¹ᵁ (t ⁻¹ᵁ U)).ι ≫ pullback.fst b t) ≫ b =
      (pullback.snd b t ∣_ (t ⁻¹ᵁ U) ≫ t ∣_ U) ≫ U.ι := by
    simp only [Category.assoc, pullback.condition, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have sq := IsPullback.of_right (h₁₁ := pullback.lift _ _ hc) (by rw [pullback.lift_fst]; exact big)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b U.ι)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq h

theorem dimLe_of_local : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  intro S A B hs Ix V g hV hA hB n T t hn
  have hcov : iSup (fun i => t ⁻¹ᵁ V i) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hV (t y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) _ hcov fun i => ?_
  by_cases hne : ∃ y, y ∈ t ⁻¹ᵁ V i
  · obtain ⟨y, hy⟩ := hne
    have : Surjective (pullback.snd A.hom t) := by haveI := hs; infer_instance
    obtain ⟨x, hx⟩ := (pullback.snd A.hom t).surjective y
    have h1 : SmoothOfRelativeDimension n (pullback.snd A.hom t ∣_ (t ⁻¹ᵁ V i)) :=
      IsZariskiLocalAtTarget.restrict hn _
    have h2 := smoothDim_restrict_pullback A.hom t (V i) (hA i)
    have e : n = g i := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2
      ⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩
    rw [e]
    exact smoothDim_restrict_pullback B.hom t (V i) (hB i)
  · push_neg at hne
    exact ⟨fun x => (hne _ x.2).elim⟩

end GlobalTheory.DualCon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDimsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relDimPreserved_of_equal_local_relDims : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  first | exact @GlobalTheory.DualCon.dimLe_of_local | exact GlobalTheory.DualCon.dimLe_of_local | (intros; apply GlobalTheory.DualCon.dimLe_of_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincare

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualExist

theorem hasRep_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] {g : ℕ} {S₁ S₂ : Over S} (e : S₁ ≅ S₂)
    (h : HasRep A g S₁) : HasRep A g S₂ := by
  obtain ⟨B, b, P, hR, hG⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩
  · obtain ⟨x, ⟨hx, hxN⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩,
      fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩
    rw [← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)
    have sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩
    have hp := hG.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [Over.comp_left]
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩

theorem hasRep_affineOpen {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {V : S.Opens}
    (hV : IsAffineOpen V) (g : ℕ) (hg : SmoothOfRelativeDimension g (pullback.snd A.hom V.ι)) :
    HasRep A g (Over.mk V.ι) := by
  let A' : Over (Sp Γ(S, V)) := (Over.pullback hV.fromSpec).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    have sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec)
        (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv)
        (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι]))
        (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback sq hg
  have h1 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (GlobalTheory.T.abelianScheme_dual_representable_affine_base _ A' g hA' hg')
  refine hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1
  show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec
  rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι]

theorem exists_dual : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  intro S A _ hA
  choose V g hV hsV hgV using GlobalTheory.T.abelianScheme_locally_constant_relDim S A hA
  have cov : ∀ s : S, ∃ i, s ∈ V i := fun s => ⟨s, hsV s⟩
  obtain ⟨B, P, hR, hGood⟩ :=
    GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))
  obtain ⟨inst, hcomm, hD, -⟩ := GlobalTheory.T.representing_additiveFamilies_isDual_comm S A B P hR
  refine ⟨B, inst, P, ?_, ?_, hD⟩
  · have hU : iSup V = ⊤ := eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩
    have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    have sq := fun i => IsPullback.of_hasPullback B.hom (V i).ι
    exact
      { comm := hcomm
        smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by
          haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _
        proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper
        geomConnected := GlobalTheory.CoverGlue.of_isPullback_cover @GeometricallyConnected hU sq fun i => (hGood i).conn }
  · have : GeometricallyConnected A.hom := hA.geomConnected
    exact GlobalTheory.T.relDimPreserved_of_equal_local_relDims S A B inferInstance S V g cov hgV fun i => (hGood i).smooth

end GlobalTheory.DualExist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_dual_abelianScheme_poincare : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  first | exact @GlobalTheory.DualExist.exists_dual | exact GlobalTheory.DualExist.exists_dual | (intros; apply GlobalTheory.DualExist.exists_dual <;> assumption)
end
end
