module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisation
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingAdd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingKernelTrivial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  first | exact @GlobalTheory.MumDesc.exists_extLam_finExt | exact GlobalTheory.MumDesc.exists_extLam_finExt | (intros; apply GlobalTheory.MumDesc.exists_extLam_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingDiagRelAmple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorAmple

open GlobalTheory.CechPic

theorem lam_rosati {K : Type} [Field K] {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {u v : B ⟶ B} (h : RosatiAdj B M u v) {T : Over (Sp K)} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ u) y = lam (cls M hM) x (y ≫ v) := by
  have e := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local K B M u v hM h
  have h1 : (cubeLB B ![fst B B ≫ u, snd B B] M).IsLB := LB.isLB_linComb hM _ _
  have h2 : (cubeLB B ![fst B B, snd B B ≫ v] M).IsLB := LB.isLB_linComb hM _ _
  have e' := (cls_eq_iff h1 h2).2 e
  rw [cls_cube_two hM, cls_cube_two hM] at e'
  have e'' := congrArg (pull (lift x y : T ⟶ G2 B).left) e'
  rw [pull_lam, pull_lam] at e''
  simpa using e''

theorem act_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O] (ρ : RingAct A O)
    (u : O) (n : ℕ) : ρ.act (n • u) = ρ.act u ^ n := by
  have h0 : ρ.act 0 = 1 := by
    have e := ρ.map_add 0 0
    rw [add_zero] at e
    have e' : ρ.act 0 * 1 = ρ.act 0 * ρ.act 0 := by rw [_root_.mul_one]; exact e.trans (Hom.mul_def _ _).symm
    exact (mul_left_cancel e').symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.map_add, ih, pow_succ]; exact (Hom.mul_def _ _).symm

theorem lam_push {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) (c : Pic G.left)
    {T : Over S'} (z w : T ⟶ H) :
    lam c (pushHom hp T z) (pushHom hp T w) = lam (pull φ c) z w := by
  simp only [lam, ← map_mul, ← map_one (pushHom hp T)]
  simp only [← pull_comp]
  rfl

end GlobalTheory.Mum.FactorAmple

namespace GlobalTheory.Mum

open GlobalTheory.CechPic GlobalTheory.Mum.FactorAmple

theorem factorPairing_diag_relAmple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ
  have := A'.isAb.comm
  have hp := isGrpPullback_pullback G (jK R)
  have hp' := isGrpPullback_pullback G' (jK R)
  let X := (Over.pullback (jK R)).obj G
  let ιK : X ⟶ (Over.pullback (jK R)).obj G' := (Over.pullback (jK R)).map inc
  let a : X ⟶ A'.A := ιK ≫ U'.gen.hom
  have hM := A'.isLB
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb hL' _ _
  have h1 := pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have h2 := pull_isLB h1 κ₀
  have h3 := pull_isLB h2 (lift (𝟙 X) (𝟙 X) : X ⟶ G2 X).left
  have e1 : pushHom hp X (𝟙 X) ≫ inc = pushHom hp' X ιK := by
    ext1
    show (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ inc.left = ιK.left ≫ pullback.fst G'.hom (jK R)
    rw [Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  have e2 : pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f =
      pushHom hp' X (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)) := by
    rw [← Category.assoc, e1]
    ext1
    show (ιK.left ≫ pullback.fst G'.hom (jK R)) ≫ (oG.act F.f).left =
      (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R)
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (ιK.left ≫ ·) (pullback.lift_fst _ _ _).symm
  have eN : cls _ h3 = lam (cls _ hL') (pushHom hp X (𝟙 X) ≫ inc) (pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f) := by
    rw [cls_pull h2, cls_pull h1, cls_pull hΛ, ← pull_comp, ← pull_comp]
    rw [← Category.assoc, FactorAdd.lift_square hp hκ, ← Over.comp_left]
    have e : cls (abelian₂ G' U'.LG.L) hΛ = lam (cls _ hL') (fst G' G') (snd G' G') := cls_cube_two hL' _ _ hΛ
    rw [e, pull_lam]
    simp
  have hgen := U'.gen_hom
  have eT : pull (pullback.fst G'.hom (jK R)) (cls _ hL') = pull U'.gen.hom.left (cls _ hM) := by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← cls_pull hL' _ (pull_isLB hL' _), ← cls_pull hM _ (pull_isLB hM _)]
    exact ((cls_eq_iff (pull_isLB hM _) (pull_isLB hL' _)).2 ⟨w, hw⟩).symm
  have eN' : cls _ h3 = lam (cls _ hM) a (a ≫ oA.act F.f) := by
    rw [eN, e2, e1, lam_push hp', eT, lam_pull]
    congr 1
    rw [Category.assoc, Category.assoc, hlin.ext F.f]
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have ha : a ≫ oA.act F.e = a := by
    show (ιK ≫ U'.gen.hom) ≫ oA.act F.e = ιK ≫ U'.gen.hom
    rw [Category.assoc, ← hlin.ext F.e, ← Category.assoc, ← Functor.map_comp, hie]
  have hΘ : ∃ t : LB.Gen (Theta A'.A A'.L), t.IsGen := GlobalTheory.GenericAmpleDvr.triv_theta A'.isAb hM
  obtain ⟨⟨b, hb, hbe⟩, -, -⟩ := hF
  have rosE : ∀ x y : X ⟶ A'.A, lam (cls _ hM) (x ≫ oA.act F.e) y = lam (cls _ hM) x (y ≫ oA.act (star F.e)) :=
    fun x y => lam_rosati hM (oA.rosati F.e) x y
  have hpow : ∀ (u : F.O) (n : ℕ), (a ≫ oA.act u) ^ n = a ≫ oA.act (n • u) := by
    intro u n
    rw [act_nsmul oA.toRingAct]
    exact (map_pow (preHom (G := A'.A) a) (oA.act u) n).symm
  have eb : b • cls _ h3 = lam (cls _ hM) a a := by
    rw [eN']
    calc b • lam (cls _ hM) a (a ≫ oA.act F.f)
        = b • lam (cls _ hM) (a ≫ oA.act F.e) ((a ≫ oA.act F.e) ≫ oA.act F.f) := by rw [ha]
      _ = b • lam (cls _ hM) a (a ≫ oA.act (star F.e * F.f * F.e)) := by
          rw [rosE, oA.map_mul, oA.map_mul]; simp only [Category.assoc]
      _ = lam (cls _ hM) a ((a ≫ oA.act (star F.e * F.f * F.e)) ^ b) := (lam_pow_right hM hΘ _ _ b).symm
      _ = lam (cls _ hM) a (a ≫ oA.act (star F.e * F.e)) := by rw [hpow, hbe]
      _ = lam (cls _ hM) (a ≫ oA.act F.e) (a ≫ oA.act F.e) := by
          rw [oA.map_mul, ← Category.assoc, ← rosE]
      _ = lam (cls _ hM) a a := by rw [ha]
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hM _ _
  have hDg := pull_isLB hΛA (lift (𝟙 A'.A) (𝟙 A'.A) : A'.A ⟶ G2 A'.A).left
  have eD : lam (cls _ hM) a a = cls _ (pull_isLB hDg a.left) := by
    have e : cls (abelian₂ A'.A A'.L) hΛA = lam (cls _ hM) (fst A'.A A'.A) (snd A'.A A'.A) := cls_cube_two hM _ _ hΛA
    rw [cls_pull hDg, cls_pull hΛA, e, pull_lam, pull_lam]
    simp
  have hNb := isLB_lbPow h3 b
  have iso := (cls_eq_iff hNb (pull_isLB hDg a.left)).1 (by rw [cls_lbPow h3, eb, eD])
  have := hG'.separated
  have : IsSeparated ((Over.pullback (jK R)).obj G').hom := by dsimp; infer_instance
  let prK : (Over.pullback (jK R)).obj G' ⟶ X := (Over.pullback (jK R)).map pr
  have hs : ιK ≫ prK = 𝟙 X := by rw [← Functor.map_comp, hip]; exact (Over.pullback (jK R)).map_id G
  have : IsSeparated prK.left := by
    have e : prK.left ≫ X.hom = ((Over.pullback (jK R)).obj G').hom := Over.w prK
    have : IsSeparated (prK.left ≫ X.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp prK.left X.hom
  have : IsClosedImmersion ιK.left := by
    have : IsClosedImmersion (ιK.left ≫ prK.left) := by
      rw [← Over.comp_left, hs]; exact inferInstanceAs (IsClosedImmersion (𝟙 _))
    exact IsClosedImmersion.of_comp ιK.left prK.left
  have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
  have : IsFinite a.left := by
    show IsFinite (ιK ≫ U'.gen.hom).left
    rw [Over.comp_left]; infer_instance
  have := A'.isAb.proper
  have : IsProper X.hom := by
    have e : a.left ≫ A'.A.hom = X.hom := Over.w a
    rw [← e]; infer_instance
  have hDgA := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A'.A hDg
    (GlobalTheory.EighthPowerFactor.relAmple_diag_lam A'.isAb hM hΘ A'.ample)
  have hNa := (hDgA.pull_of_isFinite a.left).of_lbIso hNb iso
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine X h3).2 ((GlobalTheory.isAmpleLB_pow_iff h3 hb).1 hNa)

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPush

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorSym

open GlobalTheory.CechPic GlobalTheory.EndRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def genι (G : Over (Sp R)) : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

theorem lam_push (U : UnifPre I D A G) {T : Over (Sp (FractionRing R))} (x y : T ⟶ (Over.pullback (jK R)).obj G) :
    @id (Pic T.left) (lam (T := (Over.map (jK R)).obj T) (cls _ U.LG.isLB) (push (genι G) x) (push (genι G) y)) =
      lam (cls _ A.isLB) (x ≫ U.gen.hom) (y ≫ U.gen.hom) := by
  have := U.gen_hom
  have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
  rw [cls_pull A.isLB, cls_pull U.LG.isLB] at e
  have hm : ∀ x y : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) (x * y) = push (genι G) x * push (genι G) y :=
    fun x y => push_mul (genι G) (𝟙 _) (Category.id_comp _).symm x y
  have h1 : push (genι G) (1 : T ⟶ (Over.pullback (jK R)).obj G) = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hp : ∀ x : T ⟶ (Over.pullback (jK R)).obj G,
      @id (Pic T.left) (pull (push (genι G) x).left (cls _ U.LG.isLB)) =
        pull x.left (pull U.gen.hom.left (cls _ A.isLB)) := fun x => by
    rw [e, ← pull_comp]; rfl
  rw [← lam_pull U.gen.hom, lam, lam, ← hm, ← h1, ← hp, ← hp, ← hp, ← hp]
  rfl

theorem lam_act (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.OAct O}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) {T : Over (Sp (FractionRing R))}
    (x y : (Over.map (jK R)).obj T ⟶ G) :
    lam (cls _ U.LG.isLB) (x ≫ oG.act a) y = lam (cls _ U.LG.isLB) x (y ≫ oG.act (star a)) := by
  have sj : ∀ x : (Over.map (jK R)).obj T ⟶ G, ∃ x' : T ⟶ (Over.pullback (jK R)).obj G, push (genι G) x' = x :=
    fun x => ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨x, rfl⟩ := sj x
  obtain ⟨y, rfl⟩ := sj y
  have e' : ∀ f : G ⟶ G, push (genι G) ((Over.pullback (jK R)).map f) = genι G ≫ f := fun f =>
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  rw [← push_comp _ (e' _), ← push_comp _ (e' _)]
  refine (lam_push U _ _).trans (Eq.trans ?_ (lam_push U _ _).symm)
  obtain ⟨t, ht⟩ := GlobalTheory.RosatiDescent.exists_gen_of_rosatiAdj (oA.rosati a)
  have := cls_of_rosati A.isLB t ht (x ≫ U.gen.hom) (y ≫ U.gen.hom)
  rw [Category.assoc, Category.assoc, h.ext, h.ext, ← Category.assoc, ← Category.assoc, lam, lam, this]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F hF A' G' _ _ _ U' oA oG hlin G _ _ _ inc pr _ _ hip hpi κ₀ hκ
  have hs : oG.act (star F.e * F.f * F.e) = oG.act (star F.e * star F.f * F.e) :=
    congrArg oG.act hF.2.1
  have hi : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  let GK := (Over.pullback (jK R)).obj G
  have hL := U'.LG.isLB
  have sy : ∀ x y : (Over.map (jK R)).obj (G2 GK) ⟶ G,
      lam (cls _ hL) (x ≫ inc) (y ≫ inc ≫ oG.act F.f) = lam (cls _ hL) (y ≫ inc) (x ≫ inc ≫ oG.act F.f) := fun x y => by
    have e₁ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act F.f)
    have e₂ := lam_act U'.toUnifPre hlin F.f (x ≫ inc) (y ≫ inc)
    have e₃ := lam_act U'.toUnifPre hlin F.e (x ≫ inc) (y ≫ inc ≫ oG.act (star F.f))
    have e₄ : inc ≫ oG.act F.f ≫ oG.act (star F.e) = inc ≫ oG.act (star F.f) ≫ oG.act (star F.e) := by
      have := congrArg (inc ≫ ·) hs
      simpa only [oG.map_mul, reassoc_of% hi] using this
    simp only [Category.assoc, hi] at e₁ e₂ e₃
    rw [e₁, e₄, ← e₃, ← e₂, lam_comm]
  have hP := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hL)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  refine (gen_iff_sum (pull_isLB hP κ₀) _ _).2 ?_
  rw [cls_pull hP, GlobalTheory.FullSiegel.cls_lam_pull hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← pull_comp]
  let X : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (fst GK GK)
  let Y : (Over.map (jK R)).obj (G2 GK) ⟶ G := push (genι G) (snd GK GK)
  have k₁ : κ₀ = (lift X Y).left := by
    refine pullback.hom_ext (hκ.1.trans ?_) (hκ.2.trans ?_)
    · exact (congrArg (·.left) (lift_fst X Y)).symm
    · exact (congrArg (·.left) (lift_snd X Y)).symm
  have k₂ : (lift (snd GK GK) (fst GK GK)).left ≫ κ₀ = (lift Y X).left := by
    rw [k₁]; exact lift_push (genι G) _ _
  have p₁ := pull_lam (lift X Y) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  have p₂ := pull_lam (lift Y X) (cls _ hL) (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f)
  rw [lift_fst_assoc, lift_snd_assoc] at p₁ p₂
  rw [← k₁] at p₁
  rw [← k₂] at p₂
  exact add_neg_eq_zero.2 (p₂.trans ((sy Y X).trans p₁.symm))

end GlobalTheory.Mum.FactorSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pairing_factor_mumford : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.exists_finite_extension_mumford_bundle_polarisation R hR G
    (RetractGeneric.isAbelianScheme_generic R A' G' hG' U'.gen G hG inc pr hinc hpr hip) _
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb U'.LG.isLB _ _) _)
    (FactorSym.main R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_add R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (factorPairing_diag_relAmple R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)
    (pairing_kernel_trivial R hR D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.Mum.pairing_factor_mumford | exact GlobalTheory.Mum.pairing_factor_mumford | (intros; apply GlobalTheory.Mum.pairing_factor_mumford <;> assumption)
end
end
