module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVGeneric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.GenPol

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ (A' : PolAV (Sp (FractionRing R))) (gen' : (Over.pullback (jK R)).obj G ≅ A'.A), IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have : IsCommMonObj A.A := A.isAb.comm
  have hwA : IsMonHom (oA.act w) := oA.hom w
  have hwA' : IsMonHom (oA.act (star w)) := oA.hom (star w)
  have hs : oA.act w * oA.act (star w) = 𝟙 A.A := by
    rw [Hom.mul_def]
    change padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A
    rw [← oA.map_add, hw, oA.map_one]
  have ha := (GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha
  let A' : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3,
      ample := h4, ktriv := h5 }
  refine ⟨A', U.gen, U.gen_hom, ?_⟩
  haveI := U.gen_hom
  have hLG := U.LG.isLB
  have hAL := A.isLB
  let φ := pullback.fst G.hom (jK R)
  let GK := (Over.pullback (jK R)).obj G
  let wGK := (Over.pullback (jK R)).map (oG.act w)
  have lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L) := by
    have e := GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)
    simp only [Category.comp_id] at e
    exact LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e
  have s2 := GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left
  have hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left) := by
    obtain ⟨v, hv⟩ := U.ext
    exact LBIso.symm ⟨v, hv⟩
  have hgp := isGrpPullback_of_iso U.gen
  have s3 := GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      have e := congrArg (fun q => q.left) (hlin.ext w)
      simp only [Over.comp_left] at e
      simp only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]
      exact e)
  have hpb := isGrpPullback_pullback G (jK R)
  have s4 := GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ))
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left
      rw [Category.id_comp]
      simp only [wGK, φ, Over.pullback_map_left, pullback.lift_fst])
  have s5 := GlobalTheory.RigidBundleGlue.LBIso.pull hP φ
  have e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left := by simp [pushPt]
  have e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ := Category.id_comp _
  rw [e3] at s3
  rw [e4] at s4
  have i1 := pull_isLB h1 U.gen.hom.left
  have i2 := pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left
  have i3 := lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)
  have i4 := pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ
  have i5 := pull_isLB P.L.isLB φ
  exact LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))

end GlobalTheory.Mum.GenPol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.NormLam

theorem lbIso_cubeLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

theorem lbIso_lam_adj_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP
  have hwh := oG.hom w
  have hwh' := oG.hom (star w)
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a
  have hc := fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) =
      fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x) :=
    fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G),
      GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y =
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y) :=
    fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _
      ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))
    rw [hq]
    exact GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have hN := cubeLB_isLB' ![𝟙 G, oG.act w] hM
  have hPL := P.L.isLB
  have cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB := fun x => cubeLB_isLB' x hPL
  have cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB :=
    fun x => cubeLB_isLB' x hN
  have cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB := fun x => cubeLB_isLB' x hM

  have isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L) :=
    fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)
  refine ⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩
  · exact LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _)
      (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)
  · exact LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm
      (lbIso_cubeLB' _ hP).symm)

end GlobalTheory.Mum.NormLam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.lineBundleIso_mumford_adjoint_primitive_of_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  first | exact @GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim | exact GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim | (intros; apply GlobalTheory.Mum.NormLam.lbIso_lam_adj_prim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMaps

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMapsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  first | exact @GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | exact GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | (intros; apply GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUBalanced

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem allU_balanced : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Balanced U := by
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  intro R _ _ _ I hI D A G _ _ hG U
  exact ⟨GlobalTheory.RingActData.exists_oAct GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U,
    GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U⟩

end GlobalTheory.UT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePrimitiveOfEvenNormData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum

theorem mumfordBundle_primitive_of_evenNorm_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (w : O) (ν : ℕ), w + star w = 1 → w * star w = (ν : O) → 1 ≤ ν → Even ν → TraceFormTwistIso D.toPre o w → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin w ν hw hν hν1 hev hpsi
  haveI : CharZero R := hR.2
  obtain ⟨P, hP, hE⟩ := GlobalTheory.Mum.PrimCube.exists_cp_evenOn R hR D A G hG U O o oA oG hlin w hw hpsi
  obtain ⟨A', gen', hgen, hgL⟩ := GlobalTheory.Mum.GenPol.exists_polAV_generic R hR D A G hG U O o oA oG hlin w hw hpsi P hP
  obtain ⟨D', U', hLG, -⟩ := GlobalTheory.Mum.exists_unif_even R hR G P hG hE A' gen' hgen hgL
  obtain ⟨hlam, hadj, hprim⟩ := GlobalTheory.T.lineBundleIso_mumford_adjoint_primitive_of_twist R hR D A G hG U O o oA oG hlin w hw P hP
  rw [← hLG] at hlam hadj hprim
  obtain ⟨hbal1, hbal2⟩ := GlobalTheory.UT.allU_balanced R (maximalIdeal R) hR.1 D' A' G hG U'
  obtain ⟨oA', hoA'⟩ := GlobalTheory.PELOfUnif.exists_oAct_unif U'.toUnifPre oG hadj
  obtain ⟨md, o', hlin'⟩ := hbal1 O oA' oG hoA' hadj
  letI := md
  have hpsi' : TraceFormTwistIso D'.toPre o' w := hbal2 O o' oA' oG hlin' hadj w ν hw hν hν1 hev hprim
  obtain ⟨Φ, xe, hΦ, hov, hto, hcB, hxs, hxc, hwΛ⟩ :=
    GlobalTheory.T.polarisedDegenerationData_iso_of_mumfordBundle_iso R hR D A G hG U O o oA oG hlin D' A' U' o' oA' hlin' hlam
  obtain ⟨hD, hxe, heΦ⟩ := GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso R hR D D' O o o' w hpsi hpsi' Φ xe hΦ ⟨hcB, hxs, hxc⟩ hwΛ
  obtain ⟨ψ, bc, φ, hψ, hbc, hcomp, hpu, -⟩ := GlobalTheory.unif_determined_by_data_normal R hR.1 D A G hG U D' A' G hG U' hD
  obtain ⟨hov', hto'⟩ := GlobalTheory.T.uniformisationPullbackAlongId_lies_over_dataIso R hR D A G hG U D' A' U' hD ψ.hom bc Φ.hom hψ hcomp heΦ hpu
  rw [hxe] at hto'
  have h1 : ψ.hom = 𝟙 G := GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps R hR D A G hG U D' A' U' ψ.hom (𝟙 G) Φ.hom xe.symm hψ inferInstance hov' hov hto' hto
  obtain ⟨wL, hwL, -⟩ := hpu.lg
  have hc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 G.left := by
    rw [hcomp, h1]; rfl
  have e1 : LBIso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)))) := ⟨wL, hwL⟩
  rw [hc, hLG] at e1
  have hL := U.LG.isLB
  have hPL := P.L.isLB
  have hN : (cubeLB G ![𝟙 G, oG.act w] U.LG.L).IsLB := GlobalTheory.LamCalc.cubeLB_isLB hL _
  have hL1 : (U.LG.L.pull (𝟙 G.left)).IsLB := pull_isLB hL _
  have e0 : LBIso U.LG.L (U.LG.L.pull (𝟙 G.left)) := (GlobalTheory.DescendedPrincipal.lbIso_pull_id hL).symm
  exact LBIso.trans hL hPL hN (LBIso.trans hL hL1 hPL e0 e1.symm) hP

end GlobalTheory.Mum
end
end
