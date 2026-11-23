module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeGlueLocalConditionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivialStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidified

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.AffineTrivLocus

theorem exists_closed_triv : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro R _ A _ L₀ N hA hL₀ hamp hN hrig
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp R) A L₀ hA hL₀ hamp R (𝟙 _)
      A.left (𝟙 _) A.hom (IsPullback.id_horiz A.hom)).1
  let T0 : Over (Sp R) := Over.mk (𝟙 _)
  have h₀ : IsPullback (pullback.snd T0.hom A.hom) (fst T0 A).left A.hom T0.hom :=
    (IsPullback.of_hasPullback T0.hom A.hom).flip
  obtain ⟨F, hFd⟩ : ∃ F : LB (T0 ⊗ A).left, F = N.pull (pullback.snd T0.hom A.hom) := ⟨_, rfl⟩
  have hF : F.IsLB := hFd ▸ LB.isLB_pull hN _
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv GlobalTheory.SemiRigid.globalFns R T0 A hA hproj F hF
  refine ⟨H.left, j.left, hj, ?_⟩
  intro T t A' _ φ' hφ
  let T' : Over (Sp R) := Over.mk t
  let x : T' ⟶ T0 := Over.homMk t (Category.comp_id t)
  have hR : (∃ y : T' ⟶ H, y ≫ j = x) ↔ ∃ z : T ⟶ H.left, z ≫ j.left = t := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (fun g => g.left) hy⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · change z ≫ H.hom = t
        rw [← Over.w j]
        change z ≫ j.left ≫ 𝟙 _ = t
        rw [Category.comp_id, hz]
      · exact Over.OverMorphism.ext hz
  rw [← hR, ← hH T' x]
  have h₄ : IsPullback (x ▷ A).left (fst T' A).left (fst T0 A).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  have hw : φ' ≫ A.hom = (A'.hom ≫ t) ≫ T0.hom := by
    rw [hφ.1.w]; exact (Category.comp_id _).symm
  let φ'' : A'.left ⟶ (T0 ⊗ A).left := h₀.lift φ' (A'.hom ≫ t) hw
  have hsq : IsPullback φ'' A'.hom (fst T0 A).left t := by
    refine IsPullback.of_right (h₁₂ := pullback.snd T0.hom A.hom) (h₂₂ := T0.hom) ?_ (h₀.lift_snd _ _ _) h₀
    rw [h₀.lift_fst]
    exact (Category.comp_id t).symm ▸ hφ.1
  have e₁ : (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧
      GlobalTheory.AbLaw.Triv ((F.pull (x ▷ A).left).pull ((fst T' A).left ⁻¹ᵁ U).ι)) ↔
      GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T'.left x.left := by
    rw [GlobalTheory.TrivSubscheme.locTrivOver_iff h₄]
    exact forall_congr' fun p => exists_congr fun U => and_congr_right fun _ =>
      GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _
  rw [e₁]
  show _ ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T t
  rw [GlobalTheory.TrivSubscheme.locTrivOver_iff hsq]
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  constructor
  · intro ht τ
    refine ⟨⊤, trivial, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]
    exact GlobalTheory.AbLaw.CubeOpen.triv_comp _ rfl ht
  · intro h
    refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T A' (N.pull φ') hA' (LB.isLB_pull hN φ') (GlobalTheory.PolBaseChange.rigidified_pull hφ hrig)
      fun τ => ?_
    obtain ⟨V, hV, ht⟩ := h τ
    refine ⟨V, hV, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst] at ht
    exact (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).2 ht

end GlobalTheory.AffineTrivLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidifiedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.AffineTrivLocus.exists_closed_triv | exact GlobalTheory.AffineTrivLocus.exists_closed_triv | (intros; apply GlobalTheory.AffineTrivLocus.exists_closed_triv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocu

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocusLocal


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in
theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} (N : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) :
    (∃ s : ((N.pull a).pull b).Gen, s.IsGen) ↔ ∃ s : (N.pull (b ≫ a)).Gen, s.IsGen := by
  have hb : ∀ z : Z, (b ≫ a).base z = a.base (b.base z) := fun z => rfl
  have m1 : ∀ (j : PUnit.{1} → N.ι) (z : Z), z ∈ (N.pull (b ≫ a)).U j →
      z ∈ ((N.pull a).pull b).U (fun _ _ => j PUnit.unit) := by
    intro j z hz
    have h1 : (b ≫ a).base z ∈ N.U (j PUnit.unit) := (mem_wchart_pu N (b ≫ a) j z).1 hz
    have h2 : b.base z ∈ (N.pull a).U (fun _ => j PUnit.unit) :=
      (mem_wchart_pu N a (fun _ => j PUnit.unit) (b.base z)).2 (by rw [← hb]; exact h1)
    exact (mem_wchart_pu (N.pull a) b (fun _ _ => j PUnit.unit) z).2 h2
  have m2 : ∀ (j : PUnit.{1} → PUnit.{1} → N.ι) (z : Z), z ∈ ((N.pull a).pull b).U j →
      z ∈ (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := by
    intro j z hz
    have h2 : b.base z ∈ (N.pull a).U (j PUnit.unit) := (mem_wchart_pu (N.pull a) b j z).1 hz
    have h1 : a.base (b.base z) ∈ N.U (j PUnit.unit PUnit.unit) :=
      (mem_wchart_pu N a (j PUnit.unit) (b.base z)).1 h2
    exact (mem_wchart_pu N (b ≫ a) (fun _ => j PUnit.unit PUnit.unit) z).2 (by rw [hb]; exact h1)
  constructor
  · intro h
    refine exists_gen_transfer (L := (N.pull a).pull b) (L' := N.pull (b ≫ a))
      (fun j _ _ => j PUnit.unit) m1 ?_ h
    intro i j y hy
    have hy' := pull_inf_le N (b ≫ a) i j hy
    exact (germ_pull N (b ≫ a) i j y hy hy').trans
      (germ_pull_pull N a b (fun _ _ => i PUnit.unit) (fun _ _ => j PUnit.unit) y ⟨m1 i y hy.1, m1 j y hy.2⟩ hy').symm
  · intro h
    refine exists_gen_transfer (L := N.pull (b ≫ a)) (L' := (N.pull a).pull b)
      (fun j _ => j PUnit.unit PUnit.unit) m2 ?_ h
    intro i j y hy
    have hy2 : y ∈ (N.pull (b ≫ a)).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := ⟨m2 i y hy.1, m2 j y hy.2⟩
    have hy' := pull_inf_le N (b ≫ a) _ _ hy2
    exact (germ_pull_pull N a b i j y hy hy').trans (germ_pull N (b ≫ a) _ _ y hy2 hy').symm

end GlobalTheory.TrivLocusLocal

namespace GlobalTheory.TrivLocusLocal

theorem exists_closed_triv_local : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S _ A _ L₀ N hA hL₀ ha hN hr x
  obtain ⟨R, j, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion j)
  letI : GrpObj ((Over.pullback j').obj A) := Functor.grpObjObj
  let φ₀ := pullback.fst A.hom j'
  have hp := isGrpPullback_pullback A j'
  have hB : IsAbelianScheme ((Over.pullback j').obj A) := Out.TLinPf.isAb_pullback j' A hA
  have hL₀' := pull_isLB hL₀ φ₀
  have haB : Out.RelAmple ((Over.pullback j').obj A) (L₀.pull φ₀) := by
    have := GlobalTheory.KTrivSpread.relAmple_chart j' (𝟙 _) hL₀ ha
    rwa [Category.id_comp] at this
  have hN' := pull_isLB hN φ₀
  have hrB : Out.Rigidified ((Over.pullback j').obj A) (N.pull φ₀) := by
    obtain ⟨s, hs⟩ := hr
    have h1 := exists_gen_pull_comp N (eSec A) j' ⟨s, hs⟩
    rw [← GlobalTheory.RigidBundleGlue.eSec_comm hp] at h1
    exact (exists_gen_pull_pull_iff N φ₀ (eSec ((Over.pullback j').obj A))).2 h1
  obtain ⟨Z, i₀, hi₀, H⟩ := GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified R ((Over.pullback j').obj A) (L₀.pull φ₀) (N.pull φ₀) hB hL₀' haB hN' hrB
  refine ⟨j'.opensRange, Z, i₀ ≫ j'.isoOpensRange.hom, hx, inferInstance, fun T t => ?_⟩
  let t' : T ⟶ Sp R := t ≫ j'.isoOpensRange.inv
  have ht : t' ≫ j' = t ≫ j'.opensRange.ι := by
    simp only [t', Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  letI : GrpObj ((Over.pullback t').obj ((Over.pullback j').obj A)) := Functor.grpObjObj
  have hq := isGrpPullback_pullback ((Over.pullback j').obj A) t'
  have H1 := H T t' _ _ hq
  have hP : IsPullback (pullback.fst ((Over.pullback j').obj A).hom t' ≫ φ₀)
      (pullback.snd ((Over.pullback j').obj A).hom t') A.hom (t ≫ j'.opensRange.ι) := by
    rw [← ht]
    exact (IsPullback.of_hasPullback ((Over.pullback j').obj A).hom t').paste_horiz
      (IsPullback.of_hasPullback A.hom j')
  rw [← trivCond_iff A N T (t ≫ j'.opensRange.ι) _ _ _ hP, ← exists_gen_pull_pull_iff]
  refine H1.trans ⟨fun ⟨z, hz⟩ => ⟨z, ?_⟩, fun ⟨z, hz⟩ => ⟨z, ?_⟩⟩
  · rw [← Category.assoc, hz]
    simp only [t', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [t', ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TrivLocusLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocuStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.TrivLocusLocal.exists_closed_triv_local | exact GlobalTheory.TrivLocusLocal.exists_closed_triv_local | (intros; apply GlobalTheory.TrivLocusLocal.exists_closed_triv_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivCond_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  intro S A _ N hA hN hR T t hloc Y φ y hY
  haveI := hA.comm
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  let e : Over.mk y ≅ (Over.pullback t).obj A := Over.isoMk hY.isoPullback hY.isoPullback_hom_snd
  letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk y) A t φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _)
      (by simp [e])
  have hA' : IsAbelianScheme (Over.mk y) := by
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hP.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hP.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hP.1 hA.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro U
    refine ⟨⟨fun x z => Over.OverMorphism.ext (hP.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hP.2 U x z (pushPt hP.1.w x) (pushPt hP.1.w z) rfl rfl,
      ← hP.2 U z x (pushPt hP.1.w z) (pushPt hP.1.w x) rfl rfl, _root_.mul_comm]
  haveI := hA'.comm
  obtain ⟨r, hr⟩ := hR
  have he : eSec (Over.mk y) ≫ φ = t ≫ eSec A := (cubeMapOf hP).e_comm
  have g := rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr
  have hR' : Out.Rigidified (Over.mk y) (N.pull φ) := ⟨_, g⟩
  refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)
  obtain ⟨V, hτ, hV⟩ := hloc τ
  refine ⟨V, hτ, ?_⟩
  have H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t) :=
    (isPullback_morphismRestrict y V).flip.paste_horiz hY
  exact (GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)

end GlobalTheory.TrivLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  first | (exact @GlobalTheory.TrivLocus.trivCond_of_local) | (exact GlobalTheory.TrivLocus.trivCond_of_local) | (intros; apply GlobalTheory.TrivLocus.trivCond_of_local  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedTrivialLocusRigidifiedBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ L₀ N hA hL₀ hamp hN hrig
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.closedSubscheme_glue_local_condition S (TrivCond A N) (trivCond_comp A N)
    (GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local S A N hA hN hrig) (GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus S A L₀ N hA hL₀ hamp hN hrig)
  refine ⟨Z, i, hi, fun T t A' _ φ' hP => ?_⟩
  rw [trivCond_iff A N T t A'.left φ' A'.hom hP.1]
  exact hZ T t

end GlobalTheory.TrivLocus
end
end
