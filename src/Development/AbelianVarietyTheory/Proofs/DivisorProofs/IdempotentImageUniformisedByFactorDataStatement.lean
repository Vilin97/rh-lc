module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPair
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPairStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  first | exact @GlobalTheory.MumIsoAdj.iso_of_factor_adj | exact GlobalTheory.MumIsoAdj.iso_of_factor_adj | (intros; apply GlobalTheory.MumIsoAdj.iso_of_factor_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.MumFam

theorem lbIso_lam_retract_adj : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  intro S G G' G₀ _ _ _ _ _ _ L L' L₀ hL hL' hL₀ inc u u' E E' Fm hinc hu hE huu hA hB hLL
  haveI := hinc
  haveI := hu
  have key : inc ≫ u ≫ u' = inc ≫ Fm ≫ E' := by
    rw [huu, ← Category.assoc inc E, hE]
  let P : G2 G ⟶ G2 G' := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm)
  let Q : G2 G ⟶ G' ⊗ G₀ := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ u)
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hLam' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff hLam (pull_isLB hLam' _)).1 ?_
  rw [cls_pull hLam']
  have c1 : cls (abelian₂ G L) hLam =
      GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] (cls L₀ hL₀) := by
    have e0 : cls L hL = CechPic.pull (inc ≫ u).left (cls L₀ hL₀) := (cls_eq_iff hL (pull_isLB hL₀ _)).2 hLL
    have hp : GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (CechPic.pull (inc ≫ u).left (cls L₀ hL₀)) =
        GlobalTheory.ZH.EndoExtend.cubeCls G₀ (fun i => x2 G i ≫ (inc ≫ u)) (cls L₀ hL₀) := by
      unfold GlobalTheory.ZH.EndoExtend.cubeCls
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← CechPic.pull_comp, ← Over.comp_left]
      have he := psum_hom (MonoidHom.mk' (fun z : G2 G ⟶ G => z ≫ (inc ≫ u))
        fun a b => MonObj.mul_comp a b (inc ≫ u)) (x2 G) I.down
      change psum G (x2 G) I.down ≫ (inc ≫ u) =
        psum G₀ (fun i => x2 G i ≫ (inc ≫ u)) I.down at he
      rw [he]
    rw [show cls (abelian₂ G L) hLam = GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (cls L hL) from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ hL, e0, hp]
    congr 1
    ext i
    fin_cases i <;> simp [x2]
  have c2 : CechPic.pull P.left (cls (abelian₂ G' L') hLam') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] (cls L' hL') := by
    rw [show cls (abelian₂ G' L') hLam' = GlobalTheory.ZH.EndoExtend.cubeCls G' (x2 G') (cls L' hL') from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL']
    exact GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ _ _ (fun i => by fin_cases i <;> simp [x2, P]) _
  have a1 : GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G' G₀ ≫ u, snd G' G₀] (cls L₀ hL₀) =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G₀, snd G' G₀ ≫ u'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₀ _ hL₀).symm.trans
      (((cls_eq_iff _ _).2 hA).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b1 := congrArg (CechPic.pull Q.left) a1
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G₀ _ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] Q
      (fun i => by fin_cases i <;> simp [Q]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] Q
      (fun i => by fin_cases i <;> simp [Q, key])] at b1
  have a2 : GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G' ≫ E, snd G' G'] (cls L' hL') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G', snd G' G' ≫ E'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL').symm.trans
      (((cls_eq_iff _ _).2 hB).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b2 := congrArg (CechPic.pull P.left) a2
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] P
      (fun i => by fin_cases i <;> simp [P, hE]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] P
      (fun i => by fin_cases i <;> simp [P])] at b2
  exact c1.trans (b1.trans (b2.symm.trans c2.symm))

end GlobalTheory.MumFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumFam.lbIso_lam_retract_adj | exact GlobalTheory.MumFam.lbIso_lam_retract_adj | (intros; apply GlobalTheory.MumFam.lbIso_lam_retract_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_act_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin x
  have hL : ∀ a : O, LinHom U.toUnifPre U.toUnifPre (o.onB.act a)
      (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o x
  have h₁ := linHom_iff_linEnd.1 (hL x)
  have h₂ := linHom_iff_linEnd.1 (hL (Star.star x))
  rw [star_star] at h₂
  exact GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A G hG U _ _ _ _ hE _ _ h₁ h₂

end GlobalTheory.MumFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  first | exact @GlobalTheory.MumFam.gAdj_act_star | exact GlobalTheory.MumFam.gAdj_act_star | (intros; apply GlobalTheory.MumFam.gAdj_act_star <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.MumDesc

theorem image_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hi hp hip hpi
  obtain ⟨G₀, _, _, A₀, hG₀, ⟨U₀⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨ε, u, u', hε, hu, -, he, huu, hadj⟩ :=
    GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair R hR D D' F hF A' G' hG' U' oA oG hlin G hG inc pr hi hp hip hpi A₀ G₀ hG₀ U₀
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso R hR D A₀ G G₀ ε hε hG₀ U₀
  refine ⟨A₀, U, GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs _ G G' G₀ U.LG.L U'.LG.L U₀.LG.L U.LG.isLB U'.LG.isLB U₀.LG.isLB inc u u'
    (oG.act F.e) (oG.act (Star.star F.e)) (oG.act F.f) hi hu ?_ ?_ hadj
    (GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle R hR D' A' G' hG' U' F.O F.o oA oG hlin F.e) (he ▸ hU)⟩
  · rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  · rw [huu, oG.map_mul, oG.map_mul]

end GlobalTheory.MumDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_image_uniformised_by_factor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumDesc.image_unif | exact GlobalTheory.MumDesc.image_unif | (intros; apply GlobalTheory.MumDesc.image_unif <;> assumption)
end
end
