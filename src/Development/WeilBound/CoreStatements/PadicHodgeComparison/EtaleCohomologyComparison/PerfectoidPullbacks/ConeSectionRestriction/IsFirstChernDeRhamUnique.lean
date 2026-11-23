module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowTop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChange

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeTwistingSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_chartHom {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (N : ℕ) (j : Fin (N + 1)) :
    ∃ c : ChartR R N j →+* ChartR R' N j,
      chart R' N j ≫ GlobalTheory.ProjSpace.baseChange N φ = spMap c ≫ chart R N j ∧
      ∀ k, c (ratio R N j k) = ratio R' N j k := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (_ : s = MvPolynomial.X j)
      (hd : s ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R' 1),
      ∃ ψ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s →+* ChartR R' N j,
        chart R' N j = spMap ψ ≫ Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R') s hd one_pos ∧
        ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R') (hf),
          ψ (HomogeneousLocalization.Away.mk _ hd n f hf) =
            HomogeneousLocalization.Away.mk _ (X_mem R' N j) n f hf := by
    rintro _ rfl hd
    refine ⟨RingHom.id _, ?_, fun _ _ _ => rfl⟩
    have e : spMap (RingHom.id (ChartR R' N j)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    rfl
  obtain ⟨ψ, h1, h2⟩ := key (GlobalTheory.ProjSpace.gradedMap N φ (MvPolynomial.X j)) (MvPolynomial.map_X φ j)
    ((GlobalTheory.ProjSpace.gradedMap N φ).2 (X_mem R N j))
  refine ⟨ψ.comp (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j)), ?_, fun k => ?_⟩
  · rw [h1, Category.assoc, GlobalTheory.ProjSpace.baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N j),
      ← Spec.map_comp_assoc]
    rfl
  · change ψ (HomogeneousLocalization.Away.map (GlobalTheory.ProjSpace.gradedMap N φ) (MvPolynomial.X j) _) = _
    rw [ratio, HomogeneousLocalization.Away.map_mk, h2]
    simp [ratio, GlobalTheory.ProjSpace.gradedMap]

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hO : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  obtain ⟨N, i, hi, hp, het, s, hs, hu⟩ := hO
  have H := GlobalTheory.ProjSpace.isPullback_baseChange N φ
  have hw : (pullback.fst p (spMap φ) ≫ i) ≫ PSpace.str R N = pullback.snd p (spMap φ) ≫ spMap φ := by
    rw [Category.assoc, hp]
    exact pullback.condition
  obtain ⟨i', hi1, hi2⟩ : ∃ i' : pullback p (spMap φ) ⟶ PSpace R' N,
      i' ≫ GlobalTheory.ProjSpace.baseChange N φ = pullback.fst p (spMap φ) ≫ i ∧
      i' ≫ PSpace.str R' N = pullback.snd p (spMap φ) :=
    ⟨H.lift _ _ hw, H.lift_fst _ _ hw, H.lift_snd _ _ hw⟩
  have Hl : IsPullback i' (pullback.fst p (spMap φ)) (GlobalTheory.ProjSpace.baseChange N φ) i := by
    refine IsPullback.of_right (h₁₂ := PSpace.str R' N) (v₁₃ := spMap φ) (h₂₂ := PSpace.str R N) ?_ hi1 H.flip
    rw [hi2, hp]
    exact (IsPullback.of_hasPullback p (spMap φ)).flip
  have hc : IsClosedImmersion i' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) Hl.flip hi
  choose c hc1 hc2 using fun j => exists_chartHom φ N j
  have hm : ∀ j, (pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ)) ≫ i =
      (pullback.snd i' (chart R' N j) ≫ spMap (c j)) ≫ chart R N j := fun j => by
    rw [Category.assoc, Category.assoc, ← hc1, ← hi1, ← Category.assoc, pullback.condition, Category.assoc]
  let m : ∀ j, pullback i' (chart R' N j) ⟶ pullback i (chart R N j) := fun j => pullback.lift _ _ (hm j)
  have hm1 : ∀ j, m j ≫ pullback.fst i (chart R N j) =
      pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => pullback.lift_fst _ _ _
  have hm2 : ∀ j, m j ≫ pullback.snd i (chart R N j) =
      pullback.snd i' (chart R' N j) ≫ spMap (c j) := fun j => pullback.lift_snd _ _ _
  have hl : ∀ j, (m j ≫ s j) ≫ D.f = pullback.fst i' (chart R' N j) ≫ pullback.fst p (spMap φ) := fun j => by
    rw [Category.assoc, hs, hm1]
  refine ⟨N, i', hc, hi2, ?_, fun j => pullback.lift (m j ≫ s j) (pullback.fst i' (chart R' N j)) (hl j),
    fun j => pullback.lift_snd _ _ _, ?_⟩
  · change Etale (pullback.snd D.f (pullback.fst p (spMap φ)))
    infer_instance
  · intro V j k a b h
    have h₀ : (a ≫ m j) ≫ pullback.fst i (chart R N j) = (b ≫ m k) ≫ pullback.fst i (chart R N k) := by
      rw [Category.assoc, Category.assoc, hm1, hm1, ← Category.assoc, ← Category.assoc, h]
    have e := hu V j k (a ≫ m j) (b ≫ m k) h₀
    have ueq : ∀ {a₁ a₂ b₁ b₂ : V ⟶ D.Y} (_ : a₁ = a₂) (_ : b₁ = b₂) (h₁ : a₁ ≫ D.f = b₁ ≫ D.f)
        (h₂ : a₂ ≫ D.f = b₂ ≫ D.f), D.u a₁ b₁ h₁ = D.u a₂ b₂ h₂ := by
      intro a₁ a₂ b₁ b₂ ha hb h₁ h₂
      subst ha hb
      rfl
    have nat : ∀ x, (spMap (c j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom x) =
        (Scheme.ΓSpecIso (CommRingCat.of (ChartR R' N j))).inv.hom (c j x) := fun x =>
      (congrArg (fun f => f.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (c j)))).symm
    have hs₂ : (a ≫ m j) ≫ pullback.snd i (chart R N j) =
        (a ≫ pullback.snd i' (chart R' N j)) ≫ spMap (c j) := by
      rw [Category.assoc, hm2, Category.assoc]
    refine (congrArg Units.val (ueq (by simp) (by simp) _ _)).trans (e.trans ?_)
    rw [hs₂, Scheme.Hom.comp_appTop]
    change (a ≫ pullback.snd i' (chart R' N j)).appTop.hom ((spMap (c j)).appTop.hom _) = _
    rw [nat, hc2]

end GlobalTheory.CompanionTheory.ConeTwistingSheaf
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChangeStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.twisting_sheaf_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R) (D : E.LineData X), IsTautologicalLine p D → IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback | exact GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheaf.isTwistingSheaf_pullback <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RestrictionBijectiveAboveDimension

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem isProper_of_isO1 {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    {D : E.LineData X} (hD : IsTautologicalLine p D) : IsProper p := by
  obtain ⟨N, i, hi, hip, -⟩ := hD
  exact GlobalTheory.CommonModel.isProper_of_isProjOver ⟨N, i, hi, hip⟩

theorem cls_congr {R : Type} [CommRing R] (K : Cx.{1} R) {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0)
    (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst h; rfl

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

omit [CharZero K] in
theorem ks_mono (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) : KS q s 𝒱 ≤ KS q S 𝒱 := fun T hT =>
  ⟨⟨show pdP T.δ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti T.δ h).trans (le_of_eq hT.1.1)), hT.1.2⟩, hT.2⟩

omit [CharZero K] in
theorem ks_pd (𝒱 : Set X.Opens) (s : ℕ) (c : (KS q s 𝒱).FullSubcategory) : ((KS q s 𝒱).ι.obj c).pdPow s = ⊥ :=
  c.property.1.1


def clsK (D : E.LineData X) (s : ℕ) (Λ : CLiftK (KS q s (𝒱D D)).ι D) :
    CH.H ((KS q s (𝒱D D)).ι ⋙ O (smFun X q)) 2 :=
  (CH.cx ((KS q s (𝒱D D)).ι ⋙ O (smFun X q))).cls (zK Λ s) (zK_cocycle Λ s (ks_pd q _ s))

theorem pull_cls_zK {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) (s : ℕ) (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK (Λ.precomp h) s) = 0) :
    (CH.Mor.restrict (g ⋙ O (smFun X q)) h).pull 2 ((CH.cx (g ⋙ O (smFun X q))).cls (zK Λ s) hz) =
      (CH.cx ((h ⋙ g) ⋙ O (smFun X q))).cls (zK (Λ.precomp h) s) hz' := by
  refine (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (g ⋙ O (smFun X q)) h).hom 2 (zK Λ s) hz ?_).trans ?_
  · change CH.d _ 2 ((CH.Mor.restrict (g ⋙ O (smFun X q)) h).pullC 2 (zK Λ s)) = 0
    rw [CH.Mor.d_pullC, hz, map_zero]
  · exact cls_congr _ (zK_precomp Λ h s).symm _ _

theorem clsK_res (D : E.LineData X) {s S : ℕ} (h : s ≤ S) (Λ : CLiftK (KS q s (𝒱D D)).ι D)
    (ΛS : CLiftK (KS q S (𝒱D D)).ι D) :
    (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q _ h))).pull 2
      (clsK q D S ΛS) = clsK q D s Λ := by
  have hz1 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S
      (fun c => (ks_mono q (𝒱D D) h _ c.property).1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s (ks_pd q _ s)
  refine (pull_cls_zK q ΛS _ S _ hz1).trans ((cls_congr _ ?_ hz1 hz2).trans ?_)
  · funext σ
    exact (plogK_congr _ h (ks_pd q _ s _) (r_sub_one_mem _ σ)).symm
  · exact zK_cls_eq _ Λ s (ks_pd q _ s) hz2 _

theorem pull_restrict_comp {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C']
    [Category.{0} C''] (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) (x : CH.H F n) :
    (CH.Mor.restrict F (G' ⋙ G)).pull n x = (CH.Mor.restrict (G ⋙ F) G').pull n ((CH.Mor.restrict F G).pull n x) :=
  (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict F G) (CH.Mor.restrict (G ⋙ F) G') n x).1

theorem resK_res (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) (x : HdR q 2) :
    resK q (KS q s 𝒱) 2 x = (CH.Mor.restrict ((KS q S 𝒱).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q 𝒱 h))).pull 2
      (resK q (KS q S 𝒱) 2 x) :=
  pull_restrict_comp (O (smFun X q)) (KS q S 𝒱).ι (ObjectProperty.ιOfLE (ks_mono q 𝒱 h)) 2 x

theorem restriction_bijective_above_dimension (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∀ S, d < S → Function.Bijective (resK q (KS q S (𝒱D D)) 2) := by
  have hP : IsProper q := isProper_of_isO1 hD
  obtain ⟨U, hU⟩ := (cov_ex q).2 d inferInstance
  have hcov : sSup (𝒱D D) = ⊤ := by
    obtain ⟨N, i, -, -, hi⟩ := hD
    exact sSup_𝒱D D N i hi
  intro S hS
  exact (k_iso q U S (fun α => by rw [hU]; exact hS) (𝒱D D) hcov 2).1

theorem test_factor (D : E.LineData X) (S : ℕ) (x : HdR q 2)
    (hA : ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D, resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS)
    {C : Type 1} [Category.{0} C] (g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory) {s : ℕ} (hsS : s ≤ S)
    (hs : ∀ c, ((g' ⋙ (KS q S (𝒱D D)).ι).obj c).pdPow s = ⊥) (Λ : CLiftK (g' ⋙ (KS q S (𝒱D D)).ι) D)
    (hz : CH.d _ 2 (zK Λ s) = 0) :
    (CH.cx ((g' ⋙ (KS q S (𝒱D D)).ι) ⋙ O (smFun X q))).cls (zK Λ s) hz =
      (CH.Mor.restrict (O (smFun X q)) (g' ⋙ (KS q S (𝒱D D)).ι)).pull 2 x := by
  let ΛS := (lift_exists q D S).some
  have hz1 : CH.d _ 2 (zK (ΛS.precomp g') S) = 0 :=
    zK_cocycle (ΛS.precomp g') S (fun c => (g'.obj c).property.1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp g') s) = 0 := zK_cocycle (ΛS.precomp g') s hs
  rw [pull_restrict_comp (O (smFun X q)) (KS q S (𝒱D D)).ι g' 2 x]
  change _ = (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) g').pull 2 (resK q (KS q S (𝒱D D)) 2 x)
  rw [hA ΛS]
  refine (zK_cls_eq Λ (ΛS.precomp g') s hs hz hz2).trans ?_
  refine (cls_congr _ (funext fun σ => plogK_congr _ hsS (hs _) (r_sub_one_mem _ σ)) hz2 hz1).trans ?_
  exact (pull_cls_zK q ΛS g' S _ hz1).symm

theorem isFirstChernDeRham_exists_of (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := by
  have hk := restriction_bijective_above_dimension q d D hD
  let Λ₀ := (lift_exists q D (d + 1)).some
  let x := Function.surjInv (hk (d + 1) (by omega)).2 (clsK q D (d + 1) Λ₀)
  have hx : resK q (KS q (d + 1) (𝒱D D)) 2 x = clsK q D (d + 1) Λ₀ := Function.surjInv_eq _ _
  have hA : ∀ S, d + 1 ≤ S → ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D,
      resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS := by
    intro S hS ΛS
    obtain ⟨x', hx'⟩ := (hk S (by omega)).2 (clsK q D S ΛS)
    have e : resK q (KS q (d + 1) (𝒱D D)) 2 x' = resK q (KS q (d + 1) (𝒱D D)) 2 x := by
      rw [resK_res q (𝒱D D) hS x', hx', clsK_res q D hS Λ₀ ΛS, hx]
    rw [← (hk (d + 1) (by omega)).1 e, hx']
  refine ⟨x, fun s C _ g hs hV Λ => ⟨zK Λ s, zK_cocycle Λ s hs, fun σ => rfl, ?_⟩⟩
  let S := max s (d + 1)
  let g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory := ObjectProperty.lift _ g fun c =>
    ⟨⟨show pdP _ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti _ (le_max_left _ _)).trans (le_of_eq (hs c))),
      fun r y hy => by simpa using hy⟩, by
      obtain ⟨V, σ, hσ, hV⟩ := hV c
      exact ⟨V, ⟨σ, hσ⟩, hV⟩⟩
  exact test_factor q D S x (hA S (le_max_right _ _)) g' (le_max_left _ _) hs Λ (zK_cocycle Λ s hs)

end CrystallineSemistableComparison.Pb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsFirstChernDeRhamUnique

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isO1At_exists {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N) :
    ∃ D : E.LineData X, IsTautologicalLineAt D N i := GlobalTheory.T.exists_twisting_line_data_projective N i

theorem isO1_exists {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsProjOver p) :
    ∃ D : E.LineData X, IsTautologicalLine p D := by
  obtain ⟨N, i, hi, hip⟩ := hp
  obtain ⟨D, hD⟩ := isO1At_exists N i
  exact ⟨D, N, i, hi, hip, hD⟩

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hD : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := GlobalTheory.T.twisting_sheaf_base_change φ p D hD

theorem isFirstChernDeRham_exists {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := isFirstChernDeRham_exists_of q d D hD

theorem isO1_etale {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {D : E.LineData X} (hD : IsTautologicalLine p D) :
    Etale D.f := by
  obtain ⟨N, i, -, -, h, -⟩ := hD
  exact h

theorem powK_ne_zero {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := powK_ne_zero_main q d D hD c hc

end CrystallineSemistableComparison.Pb
end
end
end
