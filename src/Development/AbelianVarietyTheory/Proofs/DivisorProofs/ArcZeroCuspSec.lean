module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBoundStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArcStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShortStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Meromorphic.Order
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomainStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulus

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulusStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus : ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  first | exact @GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | exact GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | (intros; apply GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.KeyRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_sameLie {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {e : Ix Dw → ℤ} (he : e none = 0)
    {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) {y y' : FrPt Xo c S} (h : SameLie y y') :
    evR Xo c g y' = evR Xo c g y := by
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 h.1.symm
  have h1 := (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.1 y
  let T : Ix Dw → Sˣ := fun k => k.elim a fun _ => 1
  have hb : FrBor T y y' := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 T y y').2
    ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i, fun τ i j hij => Matrix.one_apply_ne hij.ne, hc.1,
      fun τ i => h.2 τ i ▸ h1.2.1 τ i, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, Fintype.prod_option, he, zpow_zero, _root_.one_mul]
  simp [T]

end GlobalTheory.ShFam.KeyRel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroCuspSec

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

noncomputable section

namespace GlobalTheory.KoecherArc

theorem tendsto_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {e : Ix Dw → ℤ} (he : e none = 0) {g : Rul Xo c}
    (hg : g ∈ AllWt.secZ Xo c e) (hS : ∀ k, rdU U g k ∈ (U.X k).SS (la k)) {A : Type} [CommRing A] {φ : c.F →+* A}
    {x : Sp A ⟶ gen Z} (fr : EigFrame Z φ (x ≫ genι Z)) {ψ : ℂ → (A →+* ℂ)} {r : ℝ} {y : ℂ → FrPt Xo c (CAt σ)}
    (hb : IsBdArc Z σ φ x ψ r) (hm : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) (p q : A)
    (hpq : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR Xo c g (y u)) * ψ u q = ψ u p) :
    Tendsto (fun u => toC (evR Xo c g (y u))) (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨k, T, M₀, γ₀, xx, hT, hO₀, hL⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y hσ hU hb.1 hm
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E N _ T M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', h1, h2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E N _ T M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T xx hσ hU hb hm hL x₀ hx₀ x' h1 h2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E N _ T M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ :=
    GlobalTheory.T.exists_arcLift_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E N _ T M γ xx (la k) m v Lp Lm hO hlim hper
  have hp := tendsto_cusp (hS k) hO.2.2.2.1 hξ hc' ht hn
  have hsec := (hS k).1.1
  obtain ⟨hM, hΓ, hdiff, hdom, hperd⟩ := hO
  have hγd : ∀ w : ℂ, T < w.im → lact γ (xx w) ∈ (U.X k).dom := fun w hw =>
    GlobalTheory.MajInv.lact_mem_dom _ ((U.X k).Γ_stab γ hΓ) (hdom w hw)
  refine GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus (fun w => rdU U g k (xx w)) (fun _ => 0) _ (fun u => ψ u p) (fun u => ψ u q) T r M 1 1 hM
    one_pos (one_pow 1) hb.1.1.1 (hsec.1.comp hdiff hdom) (differentiableOn_const 0) (fun w hw => ?_) hp
    (hb.1.1.2 p) (hb.1.1.2 q) hpq
  obtain ⟨b, hb1, hb2, hb3⟩ := hperd w hw
  obtain ⟨h, hl⟩ := hL w hw
  refine ⟨?_, rfl, ?_⟩
  · simp only [hb3]
    rw [hsec.2.1 _ (hγd w hw) b hb1, hsec.2.2 γ hΓ _ (hdom w hw), hχ k γ hΓ]
    simp [ReciprocityTheory.ChartRestriction.G.FD.bchar, hb2]
  · rw [Complex.exp_zero, norm_one, mul_one]
    have rd : rdU U g k (xx w) = toC (evR Xo c g (U.un k ⟨xx w, h⟩)) := dif_pos h
    show ‖toC (evR Xo c g (y (eTwoPi w)))‖ = ‖rdU U g k (xx w)‖
    rw [rd, GlobalTheory.ShFam.KeyRel.evR_sameLie he hg hl]

theorem isBdArc_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z} {ψ : ℂ → (A →+* ℂ)} {r ρ : ℝ}
    (h : IsBdArc Z σ φ x ψ r) (hρ : 0 < ρ) (hρr : ρ ≤ r) : IsBdArc Z σ φ x ψ ρ :=
  ⟨⟨⟨hρ, fun a => (h.1.1.2 a).mono (Metric.ball_subset_ball hρr)⟩, h.1.2.1,
    fun u hu => h.1.2.2 u (Metric.ball_subset_ball hρr hu)⟩, h.2.1, fun u hu => h.2.2 u (Metric.ball_subset_ball hρr hu)⟩

end GlobalTheory.KoecherArc
end
end
end
