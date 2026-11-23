module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRel
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
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJetsStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioAdjointnessSeries
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLaw
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSecondPartialLawStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TangentDirectionTwoChartsLinearPartStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.chart_law_action_eq_transported_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  first | exact @GlobalTheory.ChartCmp.law_act_of_coordRel | exact GlobalTheory.ChartCmp.law_act_of_coordRel | (intros; apply GlobalTheory.ChartCmp.law_act_of_coordRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioAdjointnessSeriesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_adjointness_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → (∀ a : 𝓞 E, star a = H.bar a) → Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → FamAd t (𝟙 (Sp V)) d x B.A.act B.ad e → FamAd t (𝟙 (Sp V)) d x' B'.A.act B'.ad e' → ∀ a, JEq m (B'.ad a * ev (n := 2) ![pt V (n := 2) d 0, comp1 (B'.A.act (star a)) (pt V (n := 2) d 1)] ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] (B.ad a) * ev (n := 2) ![comp1 (B'.A.act a) (pt V (n := 2) d 0), pt V (n := 2) d 1] ε) := by
  first | exact @GlobalTheory.FrameRatioAdj.ratio_adj | exact GlobalTheory.FrameRatioAdj.ratio_adj | (intros; apply GlobalTheory.FrameRatioAdj.ratio_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLawStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_first_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh1 t (𝟙 (Sp V)) d x B.G.F B.ph1 e → FamPh1 t (𝟙 (Sp V)) d x' B'.G.F B'.ph1 e' → JEq m (B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph1 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε * ev (n := 3) ![pt V (n := 3) d 1, pt V (n := 3) d 2] ε)) := by
  first | exact @GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt | exact GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt | (intros; apply GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeries

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameRatioSym

theorem jEq_of_psJet {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] {m : ℕ} {f g : MvPowerSeries σ R}
    (h : psJet m f = psJet m g) : JEq m f g := by
  intro e he
  rw [psJet, psJet, FBIdJet.psTrunc_eq, FBIdJet.psTrunc_eq] at h
  have h' : Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (MvPowerSeries.truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) g) := h
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h'
  have := h' e (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he),
    MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he), sub_eq_zero] at this

variable {V : Type} [CommRing V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
  {d n m : ℕ} {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
  {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m} {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m}
  {y : (jOG (𝟙 (Sp V)) d m n).left} {J : ((jOG (𝟙 (Sp V)) d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem val_sy (hJ : Good t.PP.L y J) {sy : PS V 2 d} (hf : FamSy t (𝟙 (Sp V)) d x sy e) (u v : Q V d n) :
    VV m y (E2 sy u v) = (ee x e y J v u * (ee x e y J u v)⁻¹).val := by
  obtain ⟨U, hU, h⟩ := hf m
  have hc := gm_unit (y := y) U ![u, v]
  generalize hq : gm (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u, v])).left y ⊤ (unitΓ U) = c at hc
  have k : ee x e y J u v = c⁻¹ * ee x e y J v u := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·)
    (((congrArg _ (map_inv (Units.map (toΓ _).toMonoidHom) U)).trans (map_inv _ _)).trans (congrArg (·⁻¹) hq))
    (peXX hJ _ 1 0)))
  refine (hc _ hU).symm.trans (congrArg Units.val ?_)
  rw [k, mul_inv, inv_inv, mul_comm c, mul_inv_cancel_left]

theorem val_ratio (hJ : Good t.PP.L y J) (φ : Q V d 1) {ε : PS V 2 d} (hr : FrRel t x x' e e' φ.1 m ε) (u v : Q V d n) :
    VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac φ u) (ac φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := hr
  have hc := gm_unit (y := y) U ![u, v]
  have hφ : ∀ (i : Fin 2) (j : Fin d), (Ideal.Quotient.mk _ (psIn d m ![i] (φ.1 j)) : Jet V (Fin 2 × Fin d) m) =
      psJet m ((ac φ (gen i) : Q V d 2).1 j) := fun i j =>
    (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (φ.1 j))) (funext fun l => by fin_cases l; rfl))
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (φ.1 j), fun j => psIn d m ![1] (φ.1 j)]
    (ac φ (gen 0)) (ac φ (gen 1)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hφ 0 j, hφ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (φ.2 j), (cc_psIn d m _ _).trans (φ.2 j)])
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k : ee x' e' y J u v = _ * ee x e y J (ac φ u) (ac φ v) :=
    (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem frameRatio_sy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamSy t (𝟙 (Sp V)) d x B.sy e → FamSy t (𝟙 (Sp V)) d x' B'.sy e' → JEq m (B'.sy * ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] B.sy * ev (n := 2) ![pt V (n := 2) d 1, pt V (n := 2) d 0] ε) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε _ _ hi _ _ _ _ _ hr hs hs'
  let p : Q V d 1 := ⟨φ, hi.1⟩
  have key : psJet m (E2 B'.sy (gen 0 : Q V d 2) (gen 1) * E2 ε (gen 0) (gen 1)) =
      psJet m (E2 B.sy (ac p (gen 0 : Q V d 2)) (ac p (gen 1)) * E2 ε (gen 1) (gen 0)) := cst_ext fun y => by
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    have hJ' : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 2).left) y J := hJ
    show VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    rw [VV_mul, VV_mul, val_sy hJ' hs, val_sy hJ' hs', val_ratio hJ' p hr, val_ratio hJ' p hr, ← Units.val_mul,
      ← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at key
  exact jEq_of_psJet key

end GlobalTheory.FrameRatioSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeriesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_symmetry_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamSy t (𝟙 (Sp V)) d x B.sy e → FamSy t (𝟙 (Sp V)) d x' B'.sy e' → JEq m (B'.sy * ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] B.sy * ev (n := 2) ![pt V (n := 2) d 1, pt V (n := 2) d 0] ε) := by
  first | exact @GlobalTheory.FrameRatioSym.frameRatio_sy | exact GlobalTheory.FrameRatioSym.frameRatio_sy | (intros; apply GlobalTheory.FrameRatioSym.frameRatio_sy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrderStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.jetFrames_differ_by_unit_each_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  first | exact @GlobalTheory.ChartCmp.FrameRatio.main | exact GlobalTheory.ChartCmp.FrameRatio.main | (intros; apply GlobalTheory.ChartCmp.FrameRatio.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrders

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jRel_of_charts_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t hsurj d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨φ, φi, hinv, hx, -⟩ := GlobalTheory.T.exists_coordinateRelation_universalJets V t.G d x x' hu hu'
  obtain ⟨hlaw, hact⟩ := GlobalTheory.T.chart_law_action_eq_transported_of_coordRel E H V t d B B' κ κ' tg tg' uv uv' x x' φ φi hc hc' hu hinv hx
  obtain ⟨hg, h1, h2, hs, ha⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨hg', h1', h2', hs', ha'⟩ := (isFrameG_iff t _ d x' _ _ _ _ _ _ e').1 hf'
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := hinv.1
  refine ⟨φ, φi, fun m => ?_,
    GlobalTheory.T.tangentDirection_two_charts_linearPart E H V t d B B' κ κ' tg tg' uv uv' x x' φ hc hc' hu h0 hx⟩
  obtain ⟨ε, hε, hr⟩ := GlobalTheory.T.jetFrames_differ_by_unit_each_order E H V t d x x' e e' φ h0 hx hg hg' m
  exact ⟨ε, hinv, hε, hlaw, hact,
    GlobalTheory.T.frame_ratio_first_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h1 h1',
    GlobalTheory.T.frame_ratio_second_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h2 h2',
    GlobalTheory.T.frame_ratio_symmetry_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hs hs',
    GlobalTheory.T.frame_ratio_adjointness_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hstar hsurj ha ha'⟩

end GlobalTheory.ChartCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrdersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.chartsWithFrames_related_allOrders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jRel_of_charts_frames | exact GlobalTheory.ChartCmp.jRel_of_charts_frames | (intros; apply GlobalTheory.ChartCmp.jRel_of_charts_frames <;> assumption)
end
end
