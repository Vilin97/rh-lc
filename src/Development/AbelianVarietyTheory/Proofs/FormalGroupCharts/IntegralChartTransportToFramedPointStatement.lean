module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPoint
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
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.integral_frames_transport_to_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartFrameTrSt Xo c := by
  first | exact @GlobalTheory.chartFrameTransport | exact GlobalTheory.chartFrameTransport | (intros; apply GlobalTheory.chartFrameTransport <;> assumption)
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem tan_coef {V K : Type} [CommRing V] [CommRing K] [Algebra V K] {d : ℕ} (j : Fin d) :
    (jetTan ((0 : Fin 1), j) : Jet K (Fin 1 × Fin d) (0 + 1) →ₐ[K] DualNumber K).toRingHom.comp
      (jetCoef (algebraMap V K) (Fin 1 × Fin d) 1) = (dualMap (algebraMap V K)).comp
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.C r)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.C r))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro s
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.X s)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.X s))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    split_ifs <;> ext <;> simp [dualMap]


theorem chartJetTan_holds : ChartJetTanSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  intro ℓ
  obtain ⟨u, a₁, a₂⟩ := (Chart.comb_push I.m1.cart _ _ _).1 (cb ℓ)
  exact ⟨u, fun i => (a₁ i).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)), a₂.trans (h₁ _ _)⟩


theorem chartJetBasis_holds (hF : FrTanBasisSt Xo c) : ChartJetBasisSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  have := I.G.semi.smooth
  have := I.t'.semi.smooth
  let tg : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (tgT j) ((hb.1 j).1.trans (Category.comp_id _))
  have ttg : ∀ j, IsTangent (tg j) := fun j => (Chart.tan_push hid _).2 (by simp only [Category.comp_id]; exact (hb.1 j).2)
  have tD : ∀ j, IsTangent (D j) := fun j => (Chart.tan_push hid _).2 (by
    have e := congrArg (fun q => q.left) (hc.zero 1)
    refine Eq.trans ?_ (e.trans ?_)
    · rw [Category.comp_id]
      refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (xT 1).left) ((JetTr.spMap_comp' _ _).trans (congrArg spMap ?_)))
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        show (MvPolynomial.aeval _ (MvPolynomial.C r) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.C r)
        rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]; rfl
      · intro s
        show (MvPolynomial.aeval _ (MvPolynomial.X s) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.X s)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs <;> rfl
    · exact congrArg (· ≫ _) (show Spec.map (CommRingCat.ofHom (RingHom.id T.V)) ≫ 𝟙 _ = 𝟙 _ by simp))
  have eD : tg = D := funext fun j => Chart.eq_of_comb_single tD (ttg j) j
    ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hc.tan j))
  have bD : IsLieBasis D := eD ▸ ⟨ttg, fun w hw => by
    have := hb.2 w.left ⟨(Over.w w).trans (Category.comp_id _).symm, by
      simpa only [Category.comp_id] using (Chart.tan_push hid w).1 hw⟩
    simp only [Chart.comb_push hid, Category.comp_id]
    exact this⟩
  have bD' : IsLieBasis D' := Chart.isLieBasis_baseChange _ I.m2.cart bD hD
  let e := Fintype.equivFin (Lt1 Dw)
  have bU : IsLieBasis fun i => U' (e.symm i) := ⟨fun i => (Chart.tan_push I.m1.cart _).2
    ((congrArg (_ ≫ ·) (h₁ _ _)).trans (y.1.tan _ _).2), fun w hw => by
      obtain ⟨a, ha, hq⟩ := hF T.Fr y.1 (w.left ≫ I.m1.φ) ⟨Over.w (pushPt I.m1.cart.1.w w), (Chart.tan_push I.m1.cart w).1 hw⟩
      have k : ∀ b, IsLieComb b (fun i => U' (e.symm i)) w ↔ IsCombAt y.1.x (fun i => y.1.u (e.symm i).1 (e.symm i).2) b
          (w.left ≫ I.m1.φ) := fun b => (Chart.comb_push I.m1.cart _ _ _).trans (exists_congr fun u => and_congr_left'
        (forall_congr' fun i => Eq.congr_right (congrArg (_ ≫ ·) (h₁ _ _))))
      refine ⟨fun i => a (e.symm i), (k _).2 ha, fun b hb' => ?_⟩
      have := hq (fun ℓ => b (e ℓ)) (by simpa only [e, Equiv.apply_symm_apply] using (k b).1 hb')
      funext i; rw [← this]; simp⟩
  intro v
  obtain ⟨a, ha, hq⟩ := Chart.coords_basis bD' bU _ (fun i => cb (e.symm i)) v
  refine ⟨fun ℓ => a (e ℓ), fun j => (Fintype.sum_equiv e _ _ fun ℓ => by simp).trans (ha j), fun b hb' => ?_⟩
  have := hq (fun i => b (e.symm i)) fun j => (Fintype.sum_equiv e.symm _ _ fun i => rfl).trans (hb' j)
  funext ℓ; rw [← this]; simp

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrPf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)


theorem chartJetTr_of (hTan : ChartJetTanSt Xo c) (hBas : ChartJetBasisSt Xo c) : ChartJetTrSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hbas hch hdir
  letI := io.toAlgebra
  refine ⟨xU I xT, xP I xT, ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_,
    hTan T io y I d FT actT tgT uvecT xT hbas hch hdir, hBas T io y I d FT actT tgT uvecT xT hbas hch hdir⟩,
    fun m => xL_fst I xT m, fun m => rfl⟩
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = (spMap (algebraMap T.Fr T.Fr) ≫ y.1.x) ≫ η[Xo.univ.t.G].left
    rw [← Category.assoc, xL_zero I xT hch.zero m, unit_push I.m1.cart, spMap_alg_self, Category.id_comp]
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT (m + 1) ≫ I.m1.φ = xL I xT m ≫ I.m1.φ
    rw [← Category.assoc, xL_trunc I xT hch.trunc m]
  ·
    simp only [psTrunc_map]
    let W : (jO y.1 d m 2) ⟶ Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ y.1.x) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (spMap _ ≫ 𝟙 _) ≫ y.1.x = spMap _ ≫ y.1.x
        simp)
    have hj : ∀ i : Fin 2, jpt y.1 d (xU I xT) m i =
        W ≫ pushHom I.m1.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) := fun i =>
      Over.OverMorphism.ext (by
        show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
        simp)
    rw [hj 0, hj 1, ← MonObj.comp_mul, ← map_mul, ← xP_law I xT FT m (hch.law m)]
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
    simp
  ·
    simp only [psTrunc_map]
    apply Over.OverMorphism.ext
    show (xL I xT m ≫ I.m1.φ) ≫ (Xo.univ.t.act.act a).left = spMap _ ≫ xL I xT m ≫ I.m1.φ
    rw [Category.assoc, ← I.m1.act a, ← Category.assoc, xL_act I xT (actT a) a m (hch.act m a), Category.assoc]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartTransport_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartTransportSt Xo c := by
  intro E _ _ _ H Dw l Xo c _
  have hJ : ChartJetTrSt Xo c := chartJetTr_of Xo c (chartJetTan_holds Xo c)
    (chartJetBasis_holds Xo c (fun S _ _ y w hw =>
      FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw))
  have hF : ChartFrameTrSt Xo c := GlobalTheory.T.integral_frames_transport_to_framed_point E H Dw l Xo c
  have hM : FBMapSt := fbMap_holds
  intro hstar T io y I d B tgT uvecT xT eT wPT hbas hch hdir hfr hpr htr hrig
  obtain ⟨B', hF1, hA1, hp1, hp2, hsy, had⟩ := hM T.V T.Fr (algebraMap T.V T.Fr) d (𝓞 E) B
  obtain ⟨x, x', hchx, hj2, hj1⟩ := hJ T io y I d B.G.F B.A.act tgT uvecT xT hbas hch hdir
  obtain ⟨e, wP, hfrx, hprx, hrx, hfe, hwp⟩ :=
    hF hstar T io y I d B B' tgT xT eT wPT hF1 hA1 hp1 hp2 hsy had hch hfr hpr htr hrig x x' hj2 hj1
  obtain ⟨h, hh⟩ := canonGauge_exists T.Fr d (𝓞 E) T.Fr B'
  letI := io.toAlgebra
  have hchx' : IsChart y.1 d B'.G.F B'.A.act (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x := by
    have eF : B'.G.F = fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j) := funext hF1
    have eA : B'.A.act = fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j) :=
      funext fun a => funext (hA1 a)
    rw [eF, eA]
    exact hchx
  exact ⟨B', fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i), x, e, wP, h, hchx', hfrx, hprx, hh, hrx,
    ⟨hF1, hA1, hp1, hp2, hsy, had, fun ℓ i => rfl⟩, x', hj2, hj1, hfe, hwp⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.integralChart_transport_to_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartTransportSt Xo c := by
  first | exact @GlobalTheory.chartTransport_holds | exact GlobalTheory.chartTransport_holds | (intros; apply GlobalTheory.chartTransport_holds <;> assumption)
end
end
