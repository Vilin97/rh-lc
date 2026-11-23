module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrdersStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMapStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChartStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMapStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculusStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.carriesLinCombGenerator_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  first | exact @GlobalTheory.ChartCmp.carries_calculus | exact GlobalTheory.ChartCmp.carries_calculus | (intros; apply GlobalTheory.ChartCmp.carries_calculus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFr

section

@[expose] public section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem exists_corr_of_family_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    (h : φ = φ') (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c c' := by
  subst h
  refine ⟨c, hc, fun j j' _ _ hj => ?_⟩
  obtain rfl : j = j' := funext fun k => hj k k rfl
  rfl

theorem exists_pushFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  intro E _ _ _ H V _ t t' n w d x x' e hw hx he
  obtain ⟨ψ, hψ, hmon, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  haveI : IsIso n.φ := by
    rw [← hψ]
    exact inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hcar := (GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => by
    ext1
    rw [hx, Over.comp_left, hψ]
  have hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) =
      cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] := fun m => by
    funext J
    have hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) =
        fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom := by
      funext k
      fin_cases k <;> simp [jptG, hx']
    rw [hv]
    simp only [cφG, psum]
    rw [← hψ, ← Over.comp_left, foldr_padd_comp]
  have key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
      c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)])
        (cε 2) (e m) c := fun m => by
    obtain ⟨c, hc, hcc⟩ := hcar _ _
      (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)
    obtain ⟨e', he', hce⟩ := exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc
    exact ⟨e', he', c, hc, hce, hcc⟩
  choose e' he' using key
  exact ⟨e', he'⟩

end GlobalTheory.ChartCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.exists_pushFr_of_isGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  first | exact @GlobalTheory.ChartCmp.exists_pushFr | exact GlobalTheory.ChartCmp.exists_pushFr | (intros; apply GlobalTheory.ChartCmp.exists_pushFr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPush

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.PushSym

theorem val_carries {X X' Y Z : Scheme.{0}} {L' : LB X'} (L : LB X) (F : X' ⟶ X) (w : LB.Iso L' (L.pull F))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) (h : Carries L F w φ ε g g') (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι} (hJ' : Good L' z J') :
    val g' r z J = (∏ k, gm (r ≫ φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
      (w.s (fun _ => J ((r ≫ φ k) ≫ F), J' (r ≫ φ k))) ^ ε k) * val g r z J' := by
  have m1 : ∀ k, (r ≫ φ k) z ∈ (L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) := fun k =>
    Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨Set.mem_iInter.2 m1, hJ'.mem φ r⟩
  have e := congrArg (gm r z (LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓
    LB.wchart L' φ (fun k => J' (r ≫ φ k)))) (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  refine ((gm_res r z _ hm _).trans (gm_res r z _ hm.1 _)).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
    ⟨m1 k, hJ' (r ≫ φ k)⟩ _)

theorem val_scaleGenG {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

theorem prod_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T : Over X0} (a b : T ⟶ t.G) (s : T ⟶ T) (ha : s ≫ a = b) (hb : s ≫ b = a) {U : Type} [CommGroup U]
    (h : (T.left ⟶ t.G.left) → U) :
    ∏ k, h (s.left ≫ cφG t ![a, b] k) ^ cε 2 k = ∏ k, h (cφG t ![a, b] k) ^ cε 2 k := by
  have e : ∀ k, s.left ≫ cφG t ![a, b] k = cφG t ![b, a] k := fun k => by
    have := psum_hom (preHom (G := t.G) s) ![a, b] k.down
    have e2 : (fun i => preHom (G := t.G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e2] at this
    exact congrArg (fun q => q.left) this
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ cε 2 k) (e k)).trans ?_
  refine (prod_cube₂ b a h).trans (Eq.trans ?_ (prod_cube₂ a b h).symm)
  rw [_root_.mul_comm b a, mul_right_comm (h (a * b).left)]

theorem famSy_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ sy : PS V 2 d, FamSy t (𝟙 (Sp V)) d x sy e → FamSy t' (𝟙 (Sp V)) d x' sy e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' _ _ _ hP sy hs m
  obtain ⟨u, hu, hc⟩ := hs m
  obtain ⟨-, c, -, hce, hcar⟩ := hP m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  choose J' hJ' using fun χ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ'' : Good t.PP.L y J' := hJ'
  have hsub : (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) = Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.rel d ![1, 0] := by
    funext ⟨i, j⟩; fin_cases i <;> rfl
  have k := (val_corr hJ'' hc (𝟙 _)).trans ((val_scaleGenG t _ _ _ _ _ y hJ'').trans
    (congrArg₂ (· * ·) rfl (val_pull hJ'' _ _ _)))
  refine Eq.trans ?_ ((val_scaleGenG t' _ _ _ _ _ y hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm
  have v := fun r : (jOG (𝟙 (Sp V)) d m 2).left ⟶ (jOG (𝟙 (Sp V)) d m 2).left =>
    (val_corr hJ hce r).symm.trans (val_carries _ _ w _ _ _ _ hcar r y hJ hJ'')
  refine (v _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (v _)).symm)
  refine (congrArg₂ (· * ·) ?_ k).trans (mul_left_comm _ _ _)
  have p := (prod_swap t _ _ _ (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 0)
    (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 1)
    (fun ψ => gm ψ y ((t'.PP.L.pull n.φ).U (fun _ => J (ψ ≫ n.φ)) ⊓ t.PP.L.U (J' ψ)) (w.s (fun _ => J (ψ ≫ n.φ), J' ψ)))).symm
  rw [← hsub] at p
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (p.trans (Finset.prod_congr rfl fun k _ => ?_))
  · rw [Category.id_comp]; rfl
  · rw [Category.id_comp]; rfl

end GlobalTheory.PushSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPushStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.famSy_of_pushFr_cubIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ sy : PS V 2 d, FamSy t (𝟙 (Sp V)) d x sy e → FamSy t' (𝟙 (Sp V)) d x' sy e' := by
  first | exact @GlobalTheory.PushSym.famSy_push | exact GlobalTheory.PushSym.famSy_push | (intros; apply GlobalTheory.PushSym.famSy_push <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverId

section

@[expose] public section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jrel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t t' n hs d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨y, hy, hyu, hyc, hycomb⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
  obtain ⟨_, _, _, _, _, w, hw⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  obtain ⟨hg, h1, h2, h3, h4⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨f, hp⟩ := GlobalTheory.T.exists_pushFr_of_isGen E H V t t' n w d x y e hw.1 hy hg
  have hfy : IsFrameG t' (𝟙 (Sp V)) d y B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad f :=
    (isFrameG_iff t' _ d y _ _ _ _ _ _ f).2
      ⟨fun m => (hp m).1,
        GlobalTheory.T.firstPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h1,
        GlobalTheory.T.secondPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h2,
        GlobalTheory.T.famSy_of_pushFr_cubIso E H V t t' n w d x y e f hw hy hg hp _ h3,
        GlobalTheory.T.adjointness_series_transport_frames E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h4⟩
  obtain ⟨φ, φi, hj, hd⟩ := GlobalTheory.T.chartsWithFrames_related_allOrders E H hstar V t' hs d B B' κ κ' (fun l => tg l ≫ n.φ) tg' uv uv' y x' f e'
    (hyc _ _ κ tg uv hc) hc' (hyu hu) hu' hfy hf'
  exact ⟨φ, φi, hj, fun u u' v h h' => hd u u' _ (hycomb u v h) h'⟩

end GlobalTheory.ChartCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverIdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jrel_of_sabMap | exact GlobalTheory.ChartCmp.jrel_of_sabMap | (intros; apply GlobalTheory.ChartCmp.jrel_of_sabMap <;> assumption)
end
end
