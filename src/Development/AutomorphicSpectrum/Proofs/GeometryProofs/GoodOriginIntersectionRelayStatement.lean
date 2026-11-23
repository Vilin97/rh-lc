module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HoloMapProj
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsTwoTorsionWeilDegenerate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIffStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MhChange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullCst
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullDegSum
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.SmoothLogSub

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.LvExtCancel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OmLink

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem lv_ext_cancel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} {k : Type} [Field k]
    (i : Ω →+* k) {x x' : Over.mk ξ ⟶ G} (h : GenWeilModel.ext i ≫ x = GenWeilModel.ext i ≫ x') : x = x' := by
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun f => Over.Hom.left f) h
  simp only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1
  have := epi_sp i
  exact (cancel_epi _).1 h1

section obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

theorem lv_push_pow {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (a : T ⟶ G') (n : ℕ) :
    pushPt hp.1.w (a ^ n) = pushPt hp.1.w a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact push_one hp T
  | succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]

theorem lv_div (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) (y : Over.mk ξ ⟶ t.G) (hy : y ^ n = 1) :
    ∃ x : Over.mk ξ ⟶ t.G, x ^ (n * r) = 1 ∧ x ^ r = y := by
  classical
  have hp := m.cart
  let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨a, ha, hpa⟩ := pull_point hp i y hy
  obtain ⟨T⟩ := exists_tate o i
  obtain ⟨α, rfl⟩ := (T.onto n hn a).1 ha
  have hnr : 0 < n * r := Nat.mul_pos hn hr
  obtain ⟨y', -, hy'a⟩ := desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)
  let x : Over.mk ξ ⟶ t.G := Over.homMk (y'.left ≫ m.cm.F) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w y']
    simp)
  have hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α) := by
    apply Over.OverMorphism.ext
    rw [hy'a]
    simp [x, pushPt, GenWeilModel.ext, ex]
  have hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  refine ⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩
  · rw [hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]
  · rw [hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]

theorem lv_down [CharZero Ω] (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (x : Over.mk ξ ⟶ t.G) (hx : x ^ (n * r) = 1) (q : Cpt ξ) (w : Module.Dual Ω V)
    (h : M.IsHTAt t.PP.L (n * r) x q w) : M.IsHTAt t.PP.L n (x ^ r) q w := by
  obtain ⟨h0, W, f, h1, h2, h3⟩ := h
  refine ⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩
  · have hp := m.cart
    have hg' : g ^ (n * r) = 1 := by rw [pow_mul, hg, one_pow]
    obtain ⟨g₀, hg₀⟩ := hf k i g hg'
    have hg₁ : g = GenWeilModel.ext i ≫ g₀ := Over.OverMorphism.ext hg₀
    have hg₂ : g₀ ^ n = 1 := lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])
    obtain ⟨a, ha, hpa⟩ := pull_point hp i x hx
    obtain ⟨a', ha', hpa'⟩ := pull_point hp i g₀ hg₂
    have e1 : a'.left ≫ m.φ = g.left := (congrArg (fun z => z.left) hpa').trans hg₀.symm
    have e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left := congrArg (fun z => z.left) hpa
    have e3 : (a ^ r).left ≫ m.φ = xk.left := by
      have h4 := lv_push_pow hp a r
      have h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r := by
        rw [MonObj.comp_pow]
        exact h4.trans (congrArg (· ^ r) hpa)
      exact (congrArg (fun z => z.left) h5).trans hxk.symm
    refine h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1] at hc
    have hk : CharZero k := charZero_of_injective_ringHom i.injective
    have hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤)) := by
      have h6 : IsUnit ((n * r : ℕ) : k) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit
      have h7 := h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      rwa [map_natCast] at h7
    have h8 := ((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc
    rw [Nat.cast_mul]
    exact h8
  · obtain ⟨u, hu, he⟩ := h3 e v hev hv
    refine ⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩
    rw [he]
    push_cast
    ring

end obj

theorem lv_kappa {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    (hq : IsIntegrallyClosed (X.presheaf.stalk q.1)) {p : ℕ} (hp : p.Prime) {κ : Ω} (h : HT.IsCp p κ) :
    ∃ a ∈ regAt ξ q, ((p ^ 4 : ℕ) : Ω) = a * κ := by
  classical
  unfold HT.IsCp at h
  split_ifs at h with h2
  · subst h2 h
    refine ⟨4, ?_, by norm_num⟩
    simp
  · obtain ⟨ζ, hζ, rfl⟩ := h
    have hfact : Fact p.Prime := ⟨hp⟩
    have hmem : ζ ∈ primitiveRoots p Ω := (mem_primitiveRoots hp.pos).2 hζ
    have hc := congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at hc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc
    rw [← Finset.mul_prod_erase _ _ hmem] at hc
    refine ⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩
    · apply GlobalTheory.T.integral_element_regular X Ω ξ q hξ hq
      refine IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_
      refine IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_
      exact ((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos
    · push_cast
      rw [pow_succ, hc]
      ring

theorem levelFree : LevelFree := by
  intro hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq
  have hp := 𝔐.S_prime p hpS
  haveI := Fact.mk hp
  have : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono
  have hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']
    exact 𝔐.fn_over
  obtain ⟨s0, o, ⟨m⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀
  have hno := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have hnc := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree
  have hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4) := by
    rw [← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]
  have hsw := (hS q hq).2.2.1
  have hf := 𝔐.tors p hpS
  unfold HT.omP at hsw
  rw [hR] at hsw hf ⊢
  obtain ⟨a, ha, hae⟩ := lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ
  have hn : 0 < p ^ 4 := pow_pos hp.pos _
  have hr : 0 < p ^ (𝔐.R p - 4) := pow_pos hp.pos _
  generalize p ^ (𝔐.R p - 4) = r at *
  generalize p ^ 4 = n at *
  have hf' : FullTorsion 𝔐.t.G 𝔐.ξ n := fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])
  have hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e := fun N hN hfN => by
    have := GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN
      (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)
    rwa [Category.id_comp] at this
  obtain ⟨e, he⟩ := hw n hn hf'
  obtain ⟨e', he'⟩ := hw _ (Nat.mul_pos hn hr) hf
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro w ⟨z, hz, hw⟩
    obtain ⟨x, hx, rfl⟩ := lv_div o 𝔐.t m hn hr hf z hz
    obtain ⟨U, hU, w', hw'⟩ := (GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he'
      _ 𝔐.M q).1
    have h1 := hw' x hx q hU
    obtain ⟨u, hu, rfl⟩ := ((GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz
      (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw
    refine add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_
    have h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u := by
      rw [← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]
      rfl
    exact h2 ▸ Submodule.smul_mem _ _ (hsw u hu)
  · rintro w ⟨x, hx, hw⟩
    exact Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩

end LevelTowerAlt.Comparison₂
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.MolliLeOfLe

section

@[expose] public section

open MeasureTheory Metric Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (Mollifier molli coordDiv)

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem molli_le_of_le {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : ReciprocityTheory.AnForm.A.IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, φ y ≤ c) : molli ρ t φ z ≤ c := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled t y * c := by
        refine integral_mono (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z)
          ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _) fun y => ?_
        by_cases hy : ρ.scaled t y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
        have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
        rw [indicator_of_mem hmem]
        exact hc _ hmem
    _ = c := by rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem neBot_Yo (R : RegChartData A) (x : X) : (𝓝[R.Yo] x).NeBot := by
  obtain ⟨k, hk⟩ := R.cover x
  have hs := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hne := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S k) (R.chart k).open_target ((R.chart k).map_source hs)
  have ht : Tendsto (R.chart k).symm (𝓝[(R.chart k).target \ coordDiv (R.S k)] (R.chart k x)) (𝓝[R.Yo] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((R.chart k).continuousAt_symm ((R.chart k).map_source hs)).tendsto
      rw [(R.chart k).left_inv hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [R.mem_Yo k _ ((R.chart k).map_target hy.1), (R.chart k).right_inv hy.1]
      exact hy.2
  exact ht.neBot

theorem phReg_le [CompactSpace X] [T2Space X] (R : RegChartData A) (ρ : Mollifier D) (Kt : ℝ → ℝ)
    (hK : Tendsto Kt (𝓝[>] 0) atTop) {V K' : Set X} {g : X → ℝ} (hV : IsOpen V) (hg : ContinuousOn g V)
    (hph : ∀ x ∈ V ∩ R.Yo, g x = R.ph x) (hK'V : K' ⊆ V) (hK' : IsCompact K') (j : Fin R.N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K', x ∈ R.mid j → R.phReg ρ (Kt t) t j x ≤ g x + ε := by
  obtain ⟨δ, B, hδ, hT⟩ := TruncPsh.proof X D A R
  obtain ⟨U, hU, -, hUb, hUp⟩ := hT j
  set L := R.chart j '' (K' ∩ closure (R.mid j)) with hL
  have hsub : K' ∩ closure (R.mid j) ⊆ (R.chart j).source := fun x hx => R.closure_mid j hx.2
  have hLc : IsCompact L := (hK'.inter_right isClosed_closure).image_of_continuousOn ((R.chart j).continuousOn.mono hsub)
  set O := (R.chart j).target ∩ (R.chart j).symm ⁻¹' V with hO
  have hOo : IsOpen O := (R.chart j).isOpen_inter_preimage_symm hV
  have hLO : L ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(R.chart j).map_source (hsub hx), ?_⟩
    show (R.chart j).symm _ ∈ V
    rw [(R.chart j).left_inv (hsub hx)]
    exact hK'V hx.1
  let F : (Fin D → ℂ) → ℝ := fun y => R.q j y + g ((R.chart j).symm y)
  have hF : ContinuousOn F O := ((R.q_smooth j).continuousOn.mono inter_subset_left).add
    (hg.comp ((R.chart j).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2)
  obtain ⟨η, hη, hηO⟩ := hLc.exists_cthickening_subset_open hOo hLO
  obtain ⟨d, hd, hdF⟩ := Metric.uniformContinuousOn_iff.1
    ((hLc.cthickening (r := η)).uniformContinuousOn_of_continuous (hF.mono hηO)) ε hε
  obtain ⟨M, hM⟩ := hLc.exists_bound_of_continuousOn (hF.mono hLO)
  have hsm : ∀ {a : ℝ}, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun ha =>
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ha)
  filter_upwards [self_mem_nhdsWithin, hsm hδ, hsm (half_pos hη), hsm (half_pos hd), hK.eventually_ge_atTop M]
    with t ht t1 t2 t3 t4 x hx hxm
  have ht0 : (0 : ℝ) < t := ht
  have hxL : R.chart j x ∈ L := ⟨x, ⟨hx, subset_closure hxm⟩, rfl⟩
  have hxs := hsub ⟨hx, subset_closure hxm⟩
  have hFx : F (R.chart j x) = R.q j (R.chart j x) + g x := by simp only [F, (R.chart j).left_inv hxs]
  have h1 : molli ρ t (R.trunc (Kt t) j) (R.chart j x) ≤ F (R.chart j x) + ε := by
    refine molli_le_of_le ρ hU (hUp _).1 ht0 ((closedBall_subset_closedBall t1.le).trans (hUb x hxm)) fun y hy => ?_
    have hyx : dist y (R.chart j x) ≤ t := hy
    have hyO : y ∈ O := hηO (mem_cthickening_of_dist_le y _ _ _ hxL (by linarith))
    refine TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t hyO.1 ht0 fun y' hy' hy't hy'S => ?_
    have h2 : dist y' (R.chart j x) < 2 * t := by
      have := dist_triangle y' y (R.chart j x)
      have h3 : dist y' y < t := hy'
      linarith
    have hy'c : y' ∈ cthickening η L := mem_cthickening_of_dist_le y' _ _ _ hxL (by linarith)
    have h4 := hdF y' hy'c _ (self_subset_cthickening L hxL) (by linarith)
    have h5 : R.u j y' = F y' := by
      show R.q j y' + R.ph _ = R.q j y' + g _
      rw [hph _ ⟨(hηO hy'c).2, by
        rw [R.mem_Yo j _ ((R.chart j).map_target hy't), (R.chart j).right_inv hy't]
        exact hy'S⟩]
    rw [Real.dist_eq] at h4
    have h6 := hM _ hxL
    rw [Real.norm_eq_abs] at h6
    refine max_le ?_ ?_
    · rw [h5]
      linarith [(abs_lt.1 h4).2]
    · linarith [(abs_le.1 h6).1]
  show molli ρ t (R.trunc (Kt t) j) (R.chart j x) - R.q j (R.chart j x) ≤ _
  linarith

theorem regUnif : RegUnif := by
  intro K _ J _ P n M Xo B S V g hS hV hg hph
  obtain ⟨C₀, t₀, ht₀, hb⟩ := ChartMollifiedBounds.proof TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  have h3 : ∀ t x, S.regWeight t x = S.R.glue
      (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := fun _ _ => rfl
  have hup : ∀ t, 0 < t → ∀ x c, (∀ j, x ∈ S.R.mid j → S.R.phReg S.ρ (S.K t) t j x ≤ c) →
      S.regWeight t x ≤ c + S.e1 t := by
    intro t ht0 x c h
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    rw [h3]
    refine LogLogRegularisation.glue_le S.R.toPotentialCharts _ hε0 fun j hj => ?_
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t) (S.cutoff.bounds j x hj).2
    have := h j hj
    show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ c
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C₀ + 1) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x := by
    filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀), hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := hup t ht0 x C₀ fun j hj => ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
      linarith
    · have hlow : ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x := by
        intro x hx
        obtain ⟨k, hk⟩ := S.R.cover x
        have hkm := S.R.inner_subset_mid k hk
        have a1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
        have a2 := LogLogRegularisation.le_glue S.R.toPotentialCharts
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
        simp only [S.cutoff.eq_zero k x hk, mul_zero, add_zero] at a2
        rw [h3]
        linarith
      have := neBot_Yo S.R x
      have c1 : Tendsto g (𝓝[S.R.Yo] x) (𝓝 (g x)) := (hg.continuousAt (hV.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
      have c2 : Tendsto (S.regWeight t) (𝓝[S.R.Yo] x) (𝓝 (S.regWeight t x)) :=
        ((GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.continuous_of_smooth M.atlas hsm.1).tendsto x).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto c1 c2 ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy hyV
      rw [hph y ⟨hyV, hy⟩]
      exact hlow y hy
  refine ⟨⟨C₀ + 1, h1⟩, fun K' hK'V hK' => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  filter_upwards [h1, self_mem_nhdsWithin, hS.e1_tendsto_zero.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_all.2 fun j => phReg_le S.R S.ρ S.K hS.K_tendsto hV hg hph hK'V hK' j (half_pos hε)] with t a1 ht a2 a3 x hx
  have a4 := hup t ht x (g x + ε / 2) fun j hj => a3 j x hx hj
  have a5 := a1.2 x (hK'V hx)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end LevelTowerAlt.Comparison₂
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.GoodOriginTowerHeight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem LevelTowerAlt.good_origin_tower_height : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) :=
  LevelTowerAlt.Comparison₂.tie_of (LevelTowerAlt.Comparison₂.common LevelTowerAlt.Comparison₂.levelFree LevelTowerAlt.Comparison₂.muHodge) LevelTowerAlt.Comparison₂.replace (LevelTowerAlt.Comparison₂.baseSide LevelTowerAlt.Comparison₂.regUnif)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelay

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  first | exact @LevelTowerAlt.good_origin_tower_height | exact LevelTowerAlt.good_origin_tower_height
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  exact @GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay
end
end
