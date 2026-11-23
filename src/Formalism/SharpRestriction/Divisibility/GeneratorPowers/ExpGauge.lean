module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CocChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ESecToUnit
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGJAd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BqOriginSt
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.UnitIdSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhTwoValHolds
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SubstCoeRename

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGOPf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory



theorem bqOrigin : BqOriginSt := by
  unfold BqOriginSt
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C a wLa hLa wLb hLb Z r z J hJ

  have hA : ∀ e : 𝓞 E, (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act e = 1 := by
    intro e
    haveI := Xo.univ.t.act.hom e
    first
      | (simp; done)
      | (show (toUnit _ ≫ η[Xo.univ.t.G]) ≫ _ = toUnit _ ≫ η[Xo.univ.t.G]
         rw [Category.assoc, IsMonHom.one_hom])

  have hF : lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 = lift 1 (lift 1 1) := by
    first
      | (rw [show faceMap Xo.univ.t.G 2 = lift (x2 Xo.univ.t.G 0)
              (lift (x2 Xo.univ.t.G 1) (pzero Xo.univ.t.G (G2 Xo.univ.t.G))) from rfl,
            comp_lift, comp_lift,
            show x2 Xo.univ.t.G 0 = fst _ _ from rfl, show x2 Xo.univ.t.G 1 = snd _ _ from rfl,
            lift_fst, lift_snd,
            show pzero Xo.univ.t.G (G2 Xo.univ.t.G) = (1 : G2 Xo.univ.t.G ⟶ Xo.univ.t.G) from rfl,
            ExpGD.comp_one'])
      | (simp [faceMap, x2, pzero]; done)

  have hR : val C.wP (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J =
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    rw [← val_corr hJ C.prim.2 (r ≫ (toUnit (overAt y.x S)).left), val_pull hJ, Category.assoc]
    all_goals first | rfl | exact hJ
  have hP : ∀ e : 𝓞 E, val C.wP ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (Xo.univ.t.act.act e).left) z J = val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    intro e
    rw [Category.assoc, ← Over.comp_left, hA, hR]

  have hC : ∀ e₁ e₂ e₃ : 𝓞 E, val Xo.univ.t.cub.t ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃))).left) z J = 1 := by
    intro e₁ e₂ e₃
    have hm : (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫
        lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 := by
      rw [hF, comp_lift, comp_lift, hA, hA, hA]
    rw [Category.assoc, ← Over.comp_left, hm, Over.comp_left, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (Xo.univ.t.cub.face 2) _).trans ?_)
    first | exact val_one _ | exact val_one hJ _ | (simp [val_one, hJ]; done)

  have hLa0 : val wLa ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C a wLa hLa r z J hJ
  have hLb0 : val wLb ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C (H.bar a) wLb hLb r z J hJ

  have hCB : val (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left)))
      (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 := by
    refine (val_mul hJ _ _ _).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    refine (congrArg _ (val_mul hJ _ _ _)).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _),
      show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    simp

  change val (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (1 + a * H.bar a)).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ C.wP)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (a * H.bar a)).left))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act 1))).left)
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act (a * H.bar a)))).left)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left)))))
    (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1
  simp only [val_mul hJ, val_inv, val_pull hJ, hP, hR, hC, hLa0, hLb0, hJ]
  rw [hCB]
  clear hA hF hR hP hC hLa0 hLb0 hstar hLa hLb hCB
  generalize val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J = R
  group

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGUPf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

open NumberField MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FB)

section Generic

theorem map_id_apply {S σ : Type} [CommRing S] (f : MvPowerSeries σ S) : MvPowerSeries.map (algebraMap S S) f = f := by
  ext n
  simp [MvPowerSeries.coeff_map]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Type} [CommRing S] [Algebra ℚ S] {d n : ℕ} [StarRing (𝓞 E)] (B : FB S d (𝓞 E)) {h : PS S 2 d}
  (hg : B.IsCanonGauge S h)

theorem sb_expS {m : ℕ} (b : Fin m → Q S d n) {f : PS S m d} (hf : constantCoeff f = 0) :
    sb b (FB.expS S f) = FB.expS S (sb b f) := by
  rw [sb_apply, sb_apply]; exact TB.WickVanishing.gt_ev_expS _ (fun j => (b j).2) _ hf

include hg

theorem const_coeff_pair_form_zero (u v : Q S d n) : constantCoeff (E2 h u v) = 0 := by
  have := TB.LogPf.cc_ev (czQ ![(0 : Q S d 1), gen 0]) h
  rw [← sb_apply, show sb ![(0 : Q S d 1), gen 0] h = 0 from (formalSeriesValueAtTwoPoints_eq_ev h 0 (gen 0)).trans hg.ax0, map_zero] at this
  exact (congrArg constantCoeff (sb_apply _ _)).trans (TB.LogPf.constantCoeff_ev (czQ _) this.symm)

theorem cocycle_first_face_exp (u v w : Q S d n) : E3 B.ph1 u v w = FB.expS S (E2 h u w + E2 h v w - E2 h (op (FQ B.G) u v) w) := by
  have e : B.ph1 = FB.expS S (E2 h (gen 0) (gen 2) + E2 h (gen 1) (gen 2) - E2 h (op (FQ B.G) (gen 0) (gen 1)) (gen 2)) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, op_val]; exact (map_id_apply _).symm.trans (hg.ph1.trans (by rw [show B.FK S = B.G.F from funext fun _ => map_id_apply _]; rfl))
  rw [e, E3, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, map_add (f := _), formalPointSubstitutionSeries_valueAtTwoPoints, sq_op, sq_gen]; rfl

theorem cocycle_second_face_exp (u v w : Q S d n) : E3 B.ph2 u v w = FB.expS S (E2 h u v + E2 h u w - E2 h u (op (FQ B.G) v w)) := by
  have e : B.ph2 = FB.expS S (E2 h (gen 0) (gen 1) + E2 h (gen 0) (gen 2) - E2 h (gen 0) (op (FQ B.G) (gen 1) (gen 2))) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, op_val]; exact (map_id_apply _).symm.trans (hg.ph2.trans (by rw [show B.FK S = B.G.F from funext fun _ => map_id_apply _]; rfl))
  rw [e, E3, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, map_add (f := _), formalPointSubstitutionSeries_valueAtTwoPoints, sq_op, sq_gen]; rfl

omit hg [Algebra ℚ S] in
theorem actK_eq (a : 𝓞 E) : B.actK S a = B.A.act a := by
  first
  | rfl
  | (simp [FB.actK]; done)
  | (unfold FB.actK; rfl)

theorem g_ad (a : 𝓞 E) (u v : Q S d n) :
    E2 (B.ad a) u v = FB.expS S (E2 h (ac (AQ B.A a) u) v - E2 h u (ac (AQ B.A (star a)) v)) := by
  have e : B.ad a = FB.expS S (E2 h (ac (AQ B.A a) (gen 0)) (gen 1) - E2 h (gen 0) (ac (AQ B.A (star a)) (gen 1))) := by
    simp only [formalSeriesValueAtTwoPoints_eq_ev, ac_val]; exact (map_id_apply _).symm.trans ((hg.ad a).trans (by rw [actK_eq, actK_eq]; rfl))
  rw [e, E2, sb_expS _ (by simp [const_coeff_pair_form_zero B hg])]
  simp only [map_sub, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]; rfl

omit hg in
theorem g_hL (w : 𝓞 E) (u : Q S d n) : sb ![u] (B.hL S h w) = E2 h u (ac (AQ B.A w) u) := by
  have e : B.hL S h w = E2 h (gen 0) (ac (AQ B.A w) (gen 0)) := by rw [formalSeriesValueAtTwoPoints_eq_ev, ac_val, FB.hL, actK_eq]; rfl
  rw [e, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]; rfl

theorem generic (w a : 𝓞 E) :
    FB.expS S (-sb ![AQ B.A (1 + a * star a)] (B.hL S h w)) * E2 (B.ad (star a)) (AQ B.A a) (AQ B.A w) =
      E3 B.ph1 (AQ B.A 1) (AQ B.A (a * star a)) (AQ B.A ((1 + a * star a) * w)) *
        E3 B.ph2 (AQ B.A 1) (AQ B.A w) (AQ B.A (a * star a * w)) *
        E3 B.ph2 (AQ B.A (a * star a)) (AQ B.A w) (AQ B.A (a * star a * w)) * E2 (B.ad a) (AQ B.A 1) (AQ B.A (a * w)) *
        FB.expS S (-sb ![AQ B.A a] (B.hL S h w)) ^ 2 * FB.expS S (-sb ![AQ B.A 1] (B.hL S h w)) *
        FB.expS S (-sb ![AQ B.A (a * star a)] (B.hL S h w)) := by
  have g : ∀ c, ac (AQ B.A c) (gen 0 : Q S d 1) = AQ B.A c := fun c => Subtype.ext (funext fun i =>
    (congrArg (sb · (B.A.act c i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))
  have m : ∀ c c', ac (AQ B.A c) (AQ B.A c') = AQ B.A (c * c') := fun c c' => by rw [← g c', ← ac_mul, g]
  have p : ∀ c c', op (FQ B.G) (AQ B.A c) (AQ B.A c') = AQ B.A (c + c') := fun c c' => by rw [← g c, ← g c', ← ac_add, g]
  have cc := fun u v : Q S d 1 => const_coeff_pair_form_zero B hg u v
  simp only [cocycle_first_face_exp B hg, cocycle_second_face_exp B hg, g_ad B hg, g_hL, m, p, star_star, pow_two]
  repeat rw [← TB.WickVanishing.gt_expS_add _ _ (by simp [cc]) (by simp [cc])]
  congr 1
  ring_nf

end Generic

theorem unitId : UnitIdSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C φ hφ hact a
  have hsub : HasSubst fun p : Fin 1 × Fin C.d => φ p.2 := hasSubst_of_constantCoeff_zero fun p => hφ.const p.2
  let σ : PS S 1 C.d →ₐ[S] _ := substAlgHom (R := S) hsub
  have hσ : ∀ f, σ f = subst (fun p : Fin 1 × Fin C.d => φ p.2) f := fun f => congrFun (coe_substAlgHom hsub) f
  have pa : ∀ b, φa c φ b = fun j => σ (C.B.A.act b j) := fun b => funext fun j => ((hσ _).trans (hact b j)).symm
  have p1 : φ = fun j => σ (C.B.A.act 1 j) := funext fun j => by
    rw [C.B.A.one_act, hσ]; exact (subst_X hsub ((0 : Fin 1), j)).symm
  have at' : ∀ {m} (b : Fin m → Q S C.d 1) (f : PS S m C.d), σ (sb b f) = subst (fun p : Fin m × Fin C.d => σ ((b p.1).1 p.2)) f :=
    fun b f => by
      rw [hσ, sb_apply, ev, subst_comp_subst_apply (czQ b).hasSubst hsub]; simp only [hσ]
  have ex : ∀ b, σ (FB.expS S (-sb ![AQ C.B.A b] (C.B.hL S C.h H.w0))) =
      FB.expS S (-(compL (fun j => σ (C.B.A.act b j)) (C.B.hL S C.h H.w0))) := fun b => by
    have c0 : constantCoeff (-sb ![AQ C.B.A b] (C.B.hL S C.h H.w0)) = 0 := by rw [g_hL, map_neg, const_coeff_pair_form_zero C.B C.gauge, neg_zero]
    rw [hσ, FB.expS, TB.WickVanishing.subst_exp _ (fun p => hφ.const p.2) c0, ← hσ, map_neg, at']
    exact congrArg (fun q => FB.expS S (-subst q (C.B.hL S C.h H.w0))) (funext fun ⟨i, j⟩ => by fin_cases i; rfl)
  have a2 : ∀ b b' f, σ (E2 f (AQ C.B.A b) (AQ C.B.A b')) =
      atP ![fun j => σ (C.B.A.act b j), fun j => σ (C.B.A.act b' j)] f := fun b b' f =>
    (at' _ f).trans (congrArg (subst · f) (funext fun ⟨i, j⟩ => by fin_cases i <;> rfl))
  have a3 : ∀ b b' b'' f, σ (E3 f (AQ C.B.A b) (AQ C.B.A b') (AQ C.B.A b'')) =
      atP ![fun j => σ (C.B.A.act b j), fun j => σ (C.B.A.act b' j), fun j => σ (C.B.A.act b'' j)] f := fun b b' b'' f =>
    (at' _ f).trans (congrArg (subst · f) (funext fun ⟨i, j⟩ => by fin_cases i <;> rfl))
  have := congrArg σ (generic C.B C.gauge H.w0 a)
  simp only [map_mul, map_pow, ex, a2, a3, ← pa, hs] at this
  rwa [pa 1, ← p1] at this

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem expGaugeOf_of (hA : ExpActOfSt) : ExpGaugeOfSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C htr φ hφ hx
  have hact : ∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (ExpGU.actPS (Dw := Dw) c a) (φ j) := hA E H Dw l Xo c S y C φ hφ
  obtain ⟨τ, u, _, hτc, hu, hgen, hof⟩ := ExpGA.exists_eG C φ hφ.const
  refine ⟨ExpGA.eG C φ τ u, ⟨hgen, fun m => ExpGB.trunc_eG C htr φ τ u hτc hu m,
    ExpGB.rig_eG C φ hφ.const τ u hτc hu, fun a => ?_⟩, hof⟩
  have hbb : H.bar (H.bar a) = a := by rw [← hs, ← hs, star_star]
  obtain ⟨wLa, hwa, hra⟩ := ExpGD.exists_adRel C a
  obtain ⟨wLb, hwb, hrb⟩ := ExpGD.exists_adRel C (H.bar a)
  obtain ⟨β, hβ, hβ0, hβv⟩ := ExpGE.exists_beta C.wP C.prim a hbb wLa hwa wLb hwb
  exact ⟨β, hβ, hβ0, fun m => ExpGL.coc_chart ExpGJPh1.phOneVal_holds ExpGJ.phTwoVal_holds ExpGJ.adVal
    ExpGU.unitId ExpGO.bqOrigin hs C φ hφ hx hact τ u hτc hu a wLa hra wLb hrb β hβv m⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge
end
end
end
