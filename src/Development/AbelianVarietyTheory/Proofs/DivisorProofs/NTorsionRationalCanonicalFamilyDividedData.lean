module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndUOfOLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupSixTermRelationToZpowForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageNDividedPointGaloisConjEquivStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoCubeOfGeneric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.Mum.EFixCube

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cube_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J →
    ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre J D A G), IsSemiAbelian G → ∀ (x y x' y' : G ⟶ G) (cx cy cx' cy' : A.A ⟶ A.A),
    Gen₀ U U x cx → Gen₀ U U y cy → Gen₀ U U x' cx' → Gen₀ U U y' cy' →
    LBIso (cubeLB A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] A.L) (cubeLB A.A ![fst A.A A.A ≫ cx', snd A.A A.A ≫ cy'] A.L) →
    LBIso (cubeLB G ![fst G G ≫ x, snd G G ≫ y] U.LG.L) (cubeLB G ![fst G G ≫ x', snd G G ≫ y'] U.LG.L) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ hS x₁ y₁ x₂ y₂ cx₁ cy₁ cx₂ cy₂ hx₁ hy₁ hx₂ hy₂ hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ (x y : G₁ ⟶ G₁) (cx cy : A₁.A ⟶ A₁.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G₁ ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U₁.LG.L U₁.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A₁.L A₁.isLB))) := by
    intro x y cx cy hx hy
    have hL := U₁.LG.isLB
    have hA := A₁.isLB
    have hgen := U₁.gen_hom
    have hc' : CechPic.pull (pullback.fst G₁.hom (jK R)) (cls U₁.LG.L hL) =
        CechPic.pull U₁.gen.hom.left (cls A₁.L hA) := by
      obtain ⟨w, hw⟩ := U₁.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G₁ (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hA₁ := A₁.isLB
  have l₁ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₁, snd G₁ G₁ ≫ y₁] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have l₂ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₂, snd G₁ G₁ ≫ y₂] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have m₁ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have m₂ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] (cls _ hA₁) =
      cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] (cls _ hA₁) :=
    (cls_cubeLB _ _ hA₁).symm.trans (((cls_eq_iff m₁ m₂).2 hA).trans (cls_cubeLB _ _ hA₁))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ l₁ l₂ ?_
  refine (cls_eq_iff (pull_isLB l₁ _) (pull_isLB l₂ _)).1 ?_
  rw [cls_pull l₁ _ (pull_isLB l₁ _), cls_pull l₂ _ (pull_isLB l₂ _), cls_cubeLB _ _ hL₁, cls_cubeLB _ _ hL₁,
    key x₁ y₁ cx₁ cy₁ hx₁ hy₁, key x₂ y₂ cx₂ cy₂ hx₂ hy₂, eA]

theorem cube_adj_of_oLinear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G), IsSemiAbelian G → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ a : O,
    LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ U hS O _ _ _ ιD ιA ιG hl a
  have g₁ : Gen₀ U U (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hA := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local (FractionRing R) A.A A.L (ιA.act a) (ιA.act (star a)) A.isLB (ιA.rosati a)
  have := lbIso_cube_of_generic R _ hR D A G U hS (ιG.act a) (𝟙 G) (𝟙 G) (ιG.act (star a)) (ιA.act a) (𝟙 A.A) (𝟙 A.A)
    (ιA.act (star a)) (hl.ext a) g₁ g₁ (hl.ext (star a)) (by simpa only [Category.comp_id] using hA)
  simpa only [Category.comp_id] using this

end GlobalTheory.Mum.EFixCube
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EFix

theorem exists_equiv_act_of_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  intro R _ _ _ hR n hn _ Q D' F A' G' _ _ U' oA oG hS hl a _ hae p hp
  have hAdm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  haveI : CharZero R := hR.2.2.2
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨q, hqy, hqg⟩ := exists_gtPtAct (F := AlgebraicClosure (FractionRing R)) hL.1.globalFns F.o F.e p
  obtain ⟨E, eG, eA, -, -, eact⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl F.e
  obtain ⟨E', eG', -, -, eh', -⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl (star F.e)
  have hcube := GlobalTheory.Mum.EFixCube.cube_adj_of_oLinear R hAdm D' A' G' U'.toUnifPre hS F.O F.o oA oG hl F.e
  have hfun := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D' A' G' hS U'
  have h2 := (hfun.2 E E' (by rw [eG, eG']; exact hcube)).2 (AlgebraicClosure (FractionRing R))
  have hq := h2.2.2 n hn p q a (by rw [eh', star_star]; exact hqy)
    ((eact (AlgebraicClosure (FractionRing R)) _ _).2 hqg) hp
  rw [eA, hae] at hq
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D' A' G' hS U'
    (AlgebraicClosure (FractionRing R)) n hn
  exact ⟨q, hqy, hqg, (hf.2.2.1 q p).1 (((hf.1 q a).1 hq).symm.trans ((hf.1 p a).1 hp))⟩

end GlobalTheory.Mum.EFix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  first | exact @GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | exact GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed | (intros; apply GlobalTheory.Mum.EFix.exists_equiv_act_of_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGaloisFixedCanonicalNDividedFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CanonTors

theorem galois_fixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hD hQ G _ _ P hC σ x hx
  obtain ⟨-, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, hinc, hpr, hip, hpi, -⟩ := hC
  haveI : CharZero R := hCN.2.2.2
  have hadm : AdmBase R (maximalIdeal R) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ G', y = x ≫ inc := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj G',
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ n = 1 := by
    rw [hy0, ← MonObj.pow_comp, hx, MonObj.one_comp]
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ n = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  haveI := U'.gen_hom
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A, a = h ≫ U'.gen.hom := ⟨_, rfl⟩
  have ha : a ^ n = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  have hye : y ≫ oG.act F.e = y := by
    rw [hy0, ← hpi, Category.assoc, ← Category.assoc inc, hip, Category.id_comp]
  have hae : a ≫ oA.act F.e = a := by
    rw [ha0, Category.assoc, ← hlin.ext, hh0]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hye]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) n hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨p₁, hy₁, hg₁, he₁⟩ := GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion R hCN n hn hnu Q D' F A' G' U' oA oG hG' hlin a ha hae p ((hT.1 p a).2 hp.symm)
  have hf₁ : f p₁ = a := ((hT.2.2.1 p₁ p).2 he₁).trans hp
  obtain ⟨⟨p₁', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom n hn p₁
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p₁' a a' hext ha').1 ((hT.1 p₁ a).2 hf₁.symm)
  have heq := GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv T R iw s ε n hCN hn hnu ζ hζ Q e hD hQ D' F A' G' U' oA oG hG' hlin σ p p₁ p₁' hy₁ hg₁ hext
  have haa : a' = a := ((hT.1 p₁' a').1 h2).trans (((hT.2.2.1 p₁ p₁').2 heq).symm.trans hf₁)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app G').left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app G' := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ U'.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ U'.gen.hom U'.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  have := congrArg (· ≫ pr.left) hyx
  simp only [hy0, Over.comp_left, Category.assoc] at this
  rw [← Over.comp_left _ _ _ inc pr, hip, Over.id_left, Category.comp_id] at this
  exact this
end GlobalTheory.Mum.CanonTors
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGaloisFixedCanonicalNDividedFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_galoisFixed_canonical_nDivided_family : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.CanonTors.galois_fixed | exact GlobalTheory.Mum.CanonTors.galois_fixed | (intros; apply GlobalTheory.Mum.CanonTors.galois_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionRational_of_retract_galoisFixed_points : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  first | exact @GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | exact GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | (intros; apply GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torsRat_of_canon : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → TorsRat G n := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hu ζ hζ Q e hD hQB G _ _ P hC
  haveI : CharZero R := hCN.2.2.2
  have hfix := GlobalTheory.T.torsion_galoisFixed_canonical_nDivided_family T R iw s ε n hCN hn hu ζ hζ Q e hD hQB G P hC
  obtain ⟨_, D', F, A', G', _, _, U', oA, oG, inc, pr, _, _, hinc, hpr, hip, _, _⟩ := hC
  exact GlobalTheory.T.torsionRational_of_retract_galoisFixed_points G G' A' U'.gen inc pr n U'.gen_hom hinc hpr hip hn hfix

end GlobalTheory.Mum
end
end
