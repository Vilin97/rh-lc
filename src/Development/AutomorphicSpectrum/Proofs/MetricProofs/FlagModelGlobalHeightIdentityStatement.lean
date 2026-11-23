module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPuncturedStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFramePeriodsNoGlobal
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticRecentre
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.InBlockChartOfInChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.c_bm_exists_local

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def HoldsOff (Q₀ : Ideal (MRing J)) (G : Ideal (MRing J) → Prop) : Prop :=
  ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧ h ∉ Q₀ ∧ ∀ Q : Ideal (MRing J), h ∉ Q → G Q

variable {Q₀ : Ideal (MRing J)}

theorem HoldsOff.mono {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (hG : ∀ Q, G Q → G' Q) :
    HoldsOff Q₀ G' :=
  let ⟨d, f, h1, h2, h3⟩ := h
  ⟨d, f, h1, h2, fun Q hQ => hG Q (h3 Q hQ)⟩

theorem holdsOff_of_forall (hQ : Q₀.IsPrime) {G : Ideal (MRing J) → Prop} (h : ∀ Q, G Q) : HoldsOff Q₀ G :=
  ⟨0, 1, GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one, (Ideal.ne_top_iff_one _).1 hQ.ne_top, fun Q _ => h Q⟩

theorem HoldsOff.and (hQ : Q₀.IsPrime) {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (h' : HoldsOff Q₀ G') :
    HoldsOff Q₀ fun Q => G Q ∧ G' Q := by
  obtain ⟨d, f, h1, h2, h3⟩ := h
  obtain ⟨d', f', h1', h2', h3'⟩ := h'
  exact ⟨d + d', f * f', GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul h1 h1', fun h => (hQ.mem_or_mem h).elim h2 h2',
    fun Q h => ⟨h3 Q fun a => h (Q.mul_mem_right _ a), h3' Q fun a => h (Q.mul_mem_left _ a)⟩⟩

theorem holdsOff_forall (hQ : Q₀.IsPrime) {α : Type} [Finite α] {G : α → Ideal (MRing J) → Prop}
    (h : ∀ a, HoldsOff Q₀ (G a)) : HoldsOff Q₀ fun Q => ∀ a, G a Q := by
  classical
  haveI := Fintype.ofFinite α
  have key : ∀ s : Finset α, HoldsOff Q₀ fun Q => ∀ a ∈ s, G a Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact holdsOff_of_forall hQ (by simp)
    | insert a s _ ih =>
      refine (HoldsOff.and hQ (h a) ih).mono fun Q hh b hb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hh.1
      · exact hh.2 b hb
  exact (key Finset.univ).mono fun Q hh a => hh a (Finset.mem_univ a)

theorem holdsOff_regAt {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {s : Ω} (h : RegAt x Q₀ s) :
    HoldsOff Q₀ fun Q => RegAt x Q s :=
  let ⟨d, g, t, hg, ht, h0, e⟩ := h
  ⟨d, t, ht, h0, fun _ hQ => ⟨d, g, t, hg, ht, hQ, e⟩⟩

theorem inBlockChart_of_inChart {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} {c : ∀ k, J k} {q : Cpt ξ} (h : InChart ξ (segreCoord x) c q) : InBlockChart ξ x c q := by
  classical
  obtain ⟨h0, hc⟩ := h
  have h1 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 h0 k (Finset.mem_univ k)
  refine fun k => ⟨h1 k, fun i => ?_⟩
  convert hc (Function.update c k i) using 1
  unfold segreCoord
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem exists_frameDomain {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} (tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ x z w)
    {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : Ideal (MRing J) → Prop} (hG : HoldsOff (mCoordIdeal w) G) :
    ∃ f : Ω, InFrameDomain x c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord x) c p → unitAt ξ p f → InBlockChart ξ x c p ∧ G (ptIdeal ξ x p) := by
  obtain ⟨d, h, hd, h0, hG⟩ := hG
  refine ⟨MvPolynomial.aeval x h / ∏ k, x ⟨k, c k⟩ ^ d k, ⟨hc, _,
    (GlobalTheory.T.valAt_iff_value_at Z Ω ξ K J x tie z w hz hw _ _).1 (valAt_form hw hz hc hd), ?_⟩, fun p hp hu => ?_⟩
  · rw [form_mem_mCoordIdeal_iff w hd] at h0
    exact div_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  · have hb := inBlockChart_of_inChart hp
    refine ⟨hb, hG _ ?_⟩
    obtain ⟨R, _, z', w', e, hw', -⟩ := exists_ptIdeal_eq tie p
    have hz' : genPt ξ ⤳ centre z' := e ▸ p.2
    obtain rfl : p = ⟨centre z', hz'⟩ := Subtype.ext e.symm
    have hc' := (inBlockChart_centre_iff hw' hz' c).1 hb
    rw [ptIdeal_centre hw' hz', form_mem_mCoordIdeal_iff w' hd]
    rw [unitAt_iff_of_valAt (valAt_form hw' hz' hc' hd) hz'] at hu
    intro h1
    exact hu (by rw [h1, zero_div])

theorem exists_goodDomain {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} [Finite Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)
    (F : FrameData ι Ψ N M.Ω M.blk) {Z : Scheme.{0}} {ξ : Spec (CommRingCat.of M.Ω) ⟶ Z}
    (tie : CoordTie ℤ ξ fun c' : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k => ∏ k, M.x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ M.x z w) (hF : M.GoodAt F (mCoordIdeal w)) :
    ∃ f : M.Ω, InFrameDomain M.x F.c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord M.x) F.c p → unitAt ξ p f → M.GoodAt F (ptIdeal ξ M.x p) := by
  have hP : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := by
    refine (inBlockChart_centre_iff hw hz F.c).1 ((inBlockChart_iff_X_notMem tie _ F.c).2 ?_)
    rw [ptIdeal_centre hw hz]
    exact hF.1
  have h1 : HoldsOff (mCoordIdeal w) fun Q => ∀ q I, RegAt M.x Q (F.u q I) ∧ RegAt M.x Q (F.u' I q) :=
    holdsOff_forall hP fun q => holdsOff_forall hP fun I =>
      HoldsOff.and hP (holdsOff_regAt (hF.2.1 q I).1) (holdsOff_regAt (hF.2.1 q I).2)
  have h2 : HoldsOff (mCoordIdeal w) fun Q => ∀ p, M.blk p = none →
      F.υ p ≠ 0 ∧ RegAt M.x Q (F.υ p) ∧ RegAt M.x Q (F.υ p)⁻¹ := by
    refine holdsOff_forall hP fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := hF.2.2 p hp
      exact (HoldsOff.and hP (holdsOff_regAt b) (holdsOff_regAt c)).mono fun Q h _ => ⟨a, h⟩
    · exact holdsOff_of_forall hP fun Q h => absurd h hp
  obtain ⟨f, hf, hg⟩ := exists_frameDomain tie hz hw hc (HoldsOff.and hP h1 h2)
  exact ⟨f, hf, fun p a b => ⟨(inBlockChart_iff_X_notMem tie p F.c).1 (hg p a b).1, (hg p a b).2⟩⟩

end PositivityTheory.Xgp.c_bm_exists_local
end
end

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_local

open GlobalTheory.CompanionTheory.Ar.HodgeMetric Filter Topology

theorem logR_le {n a : ℕ} {w₀ w : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} {m : Fin n → ℕ} (hm : ∀ i ∈ S, 1 ≤ m i) (hw : ‖w‖ ≤ 2) (hS : ∀ i ∈ S, w i ≠ 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a → π.symm i ∈ S ∧ w₀ (π.symm i) = 0) :
    (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0) ≤ rLoc S m w := by
  have hg : ∀ j ∈ S, 0 ≤ Real.log (4 / ‖w j‖ ^ 2) := by
    intro j hj
    apply Real.log_nonneg
    have h0 : 0 < ‖w j‖ := norm_pos_iff.2 (hS j hj)
    have h2 : ‖w j‖ ≤ 2 := (norm_le_pi_norm w j).trans hw
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hinv : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).2 hρ1
  have hterm : ∀ i : Fin n, (i : ℕ) < a →
      Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) ≤ Real.log (4 / ‖w (π.symm i)‖ ^ 2) := by
    intro i hi
    obtain ⟨hS', h0'⟩ := ha i hi
    have hpos : 0 < ‖w (π.symm i)‖ := norm_pos_iff.2 (hS _ hS')
    have hu : ‖uncentre w₀ ρ π w i‖ = ρ⁻¹ * ‖w (π.symm i)‖ := by
      simp [uncentre, h0', norm_mul, abs_of_pos hρ]
    have hx : ‖w (π.symm i)‖ ≤ ρ⁻¹ * ‖w (π.symm i)‖ := by nlinarith
    apply Real.log_le_log
    · rw [hu]
      positivity
    · rw [hu, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  unfold rLoc
  refine add_le_add le_rfl ?_
  calc (∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if (i : ℕ) < a then Real.log (4 / ‖w (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h
        · exact hterm i h
        · exact le_rfl
    _ = ∑ j : Fin n, if ((π j : Fin n) : ℕ) < a then Real.log (4 / ‖w j‖ ^ 2) else 0 := by
        rw [← Equiv.sum_comp π]
        simp
    _ = ∑ j ∈ Finset.univ.filter (fun j => ((π j : Fin n) : ℕ) < a), Real.log (4 / ‖w j‖ ^ 2) :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ j ∈ S, Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j hj _ => hg j hj)
        have := (ha (π j) (Finset.mem_filter.1 hj).2).1
        simpa using this
    _ ≤ ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact le_mul_of_one_le_left (hg j hj) (by exact_mod_cast hm j hj)

theorem exists_hasFDerivAt_uncentre {n : ℕ} (w₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ∃ A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ), ∀ w, HasFDerivAt (uncentre w₀ ρ π) A w := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => (ρ : ℂ)⁻¹ • ContinuousLinearMap.proj (R := ℂ) (π.symm i)
  refine ⟨L.restrictScalars ℝ, fun w => ?_⟩
  have hf : uncentre w₀ ρ π = fun t => L.restrictScalars ℝ t - L.restrictScalars ℝ w₀ := by
    funext t i
    simp [uncentre, L, mul_sub]
  rw [hf]
  exact (L.restrictScalars ℝ).hasFDerivAt.sub_const _

theorem posDef_of_inv {N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℂ} {c : ℝ} (hc : 0 < c)
    (h : (Γ⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) : Γ.PosDef := by
  have h1 : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast hc)
  have h2 := h1.add_posSemidef h
  rw [add_sub_cancel] at h2
  exact Matrix.posDef_inv_iff.1 h2

theorem psd_mono {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {r r' : ℝ} (hr : r ≤ r')
    (h : (((r : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef) :
    (((r' : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef := by
  have hI : ((((r' - r : ℝ)) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 hr)
  have h2 := h.add hI
  convert h2 using 1
  simp only [Complex.ofReal_sub, sub_smul]
  abel

end PositivityTheory.Xgp.c_bm_exists_local
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentity

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder



open PositivityTheory.Xgp.c_bm_exists_local GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  intro _ E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb L s Bat _ _ hnorm hAd hInt F hF τ k w₀ hw₀ hgood
  classical
  obtain ⟨hAB, hball, -, M₀, hM⟩ := hAd
  obtain ⟨S₀, m, hm, hS, hr⟩ := hM k
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have uniq : ∀ {z z' : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w}, CoordsAt 𝔐.ξ M.x z w → CoordsAt 𝔐.ξ M.x z' w → z = z' :=
    fun {z z' w} h h' => (tp.1 w h.1 (tp.2.2 z w (𝔐.all _) h).1).unique ⟨𝔐.all _, h⟩ ⟨𝔐.all _, h'⟩
  have orb : ∀ {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w w'}, CoordsAt 𝔐.ξ M.x z w → SameOrbit w' w →
      CoordsAt 𝔐.ξ M.x z w' := fun {z w w'} h ⟨a, ha, e⟩ =>
    ((tp.2.2 z w (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), e⟩
  have pts : ∀ w ∈ mcPts (mCoordIdeal M.x), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  have gfn : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w Γ, CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z →
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ → HodgeMetric.gramFn 𝔐 (gb tie F τ) w = Γ := by
    intro z w Γ hw hi hΓ
    have hex : ∃ (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ := ⟨Γ, z, hw, hi, hΓ⟩
    unfold HodgeMetric.gramFn
    rw [dite_eq_left hex]
    obtain ⟨z₀, hw₀, hi₀, hΓ₀⟩ := hex.choose_spec
    rw [uniq hw₀ hw] at hΓ₀
    exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ hΓ
  let Bd : Set ((Σ k, baseIdx ι M.blk k) → ℂ) :=
    {w | ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w → ¬ 𝔐.Interior z}
  have hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ M.x z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z) :=
    fun z w hz => ⟨fun h => h z hz, fun h z' hz' => uniq hz hz' ▸ h⟩
  have hZ : ∀ x₀, ∀ x ∈ Rb.U x₀, Rb.lift x₀ x ∈ Bd ↔ x ∈ bdry s := by
    intro x₀ x hx
    obtain ⟨z, hz⟩ := pts _ (Rb.mem x₀ x hx)
    rw [hBd z _ hz, ← hInt x z (orb hz (Rb.compat x x₀ x ⟨Rb.mem_U x, hx⟩)), not_not]
  have hw₀' : ‖w₀‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 hw₀
  have hw₀t : w₀ ∈ (Bat.chart k).target := hball k (mem_closedBall_zero_iff.2 (by linarith))
  obtain ⟨ρ, π, χ, hρ, hρ', hU, hγ, ha⟩ := exists_sncChart Rb Bat hAB k w₀ hw₀t Bd (bdry s) S₀ hS hZ
  have hγ0 : χ.γ 0 = Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀) := by
    rw [hγ, HodgeMetric.recentre_zero]
  obtain ⟨z₀, hz₀⟩ := pts _ (Rb.mem _ _ (Rb.mem_U ((Bat.chart k).symm w₀)))
  obtain ⟨f, hf, hfg⟩ := exists_goodDomain M F 𝔐.tie (𝔐.all _) hz₀ hgood
  obtain ⟨a₀, g, Λ, _, LP, π', ρ', U, hP⟩ := exists_isFramePeriods_noGlobal E H D Xo l c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) _
    (gbS tie F τ) n Bd χ 0 F.c f hBd (Metric.mem_ball_self one_pos)
    (fun p h1 h2 => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ p (hfg p h1 h2))
    (hγ0 ▸ hf)
  obtain ⟨ε, c₀, C, hε, hερ, hc₀, hC, hb⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ g _ χ.a Λ LP U 0 π' ρ' hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.1 hP.2.2.2.2.1
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_uncentre w₀ ρ π
  have hcu : Continuous (HodgeMetric.uncentre w₀ ρ π) := (HodgeMetric.contDiff_uncentre w₀ ρ π).continuous
  have hcu' : Continuous (HodgeMetric.uncentre 0 ρ' π') := (HodgeMetric.contDiff_uncentre 0 ρ' π').continuous

  have pg : ∀ w ∈ Metric.ball w₀ ρ, HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 →
      baseGram tie F τ Rb ((Bat.chart k).symm w) =
        HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w)) := by
    intro w hw hu
    obtain ⟨hb1, -, hbd, hg⟩ := hP.2.2.2.2.2 _ hu.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ] at hbd hg
    obtain ⟨z, hz⟩ := pts _ (Rb.mem _ _ (hU w hw).2)
    have hi : 𝔐.Interior z := by_contra fun h => hbd.2 hu ((hBd z _ hz).2 h)
    exact gfn z _ _ (orb hz (Rb.compat _ _ _ ⟨Rb.mem_U _, (hU w hw).2⟩)) hi (hg hu z hz)
  have h0 : ∀ᶠ w in nhds w₀, ‖HodgeMetric.uncentre w₀ ρ π w - 0‖ < ε := by
    have : ContinuousAt (fun w => ‖HodgeMetric.uncentre w₀ ρ π w - 0‖) w₀ := by fun_prop
    refine this.eventually_lt continuousAt_const ?_
    simpa [HodgeMetric.uncentre_self] using hε
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 h0
  refine ⟨min ε₁ ρ, c₀, C * (1 + |M₀|) + C * Real.exp (|M₀| / 2) * ‖A‖, lt_min hε₁ hρ, hc₀, by positivity,
    fun w hw hwb => ?_⟩
  have hwρ : ‖w - w₀‖ < ρ := hw.trans_le (min_le_right _ _)
  have hwB : w ∈ Metric.ball w₀ ρ := mem_ball_iff_norm.2 hwρ
  have ht := hb₁ w (mem_ball_iff_norm.2 (hw.trans_le (min_le_left _ _)))
  have ht1 := HodgeMetric.uncentre_mem_ball hρ π hwρ
  have hub := HodgeMetric.uncentre_mem_ball hP.1 π' (ht.trans_le hερ)
  have hu : HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 := by
    have hcl := (hP.2.2.2.2.2 _ hub).2.2.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ, hZ _ _ (hU w hwB).2] at hcl
    exact hcl.1 hwb
  obtain ⟨b1, b2, b3⟩ := hb _ ht (mem_ball_zero_iff.1 ht1) hu
  have hev : ∀ᶠ w' in nhds w, baseGram tie F τ Rb ((Bat.chart k).symm w') =
      HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w')) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwB,
      (hcu'.comp hcu).continuousAt.eventually ((HodgeMetric.isOpen_punct n a₀ 1).mem_nhds hu)] with w' h1 h2
    exact pg w' h1 h2
  have hw2 : ‖w‖ ≤ 2 := by
    have := norm_add_le (w - w₀) w₀
    rw [sub_add_cancel] at this
    linarith
  have hlog := logR_le hρ (by linarith) hm hw2
    (fun i hi h => hwb ((hS w (hU w hwB).1).2 ⟨i, hi, h⟩)) ha
  have hrM := abs_le.1 ((hr w (mem_closedBall_zero_iff.2 hw2) hwb).trans (le_abs_self M₀))
  have hre : 1 ≤ rW L s ((Bat.chart k).symm w) := by
    have := hnorm ((Bat.chart k).symm w)
    have h2 := Real.add_one_le_exp (1 : ℝ)
    unfold rW
    linarith
  generalize (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < χ.a then
    Real.log (1 / ‖HodgeMetric.uncentre w₀ ρ π w i‖ ^ 2) else 0) = R at b2 b3 hlog
  generalize rW L s ((Bat.chart k).symm w) = r at hrM hre ⊢
  have hR : R ≤ r + |M₀| := by linarith [hrM.1]
  have hM0 := abs_nonneg M₀
  have hX : 0 ≤ C * Real.exp (|M₀| / 2) * ‖A‖ := by positivity
  rw [hev.self_of_nhds]
  refine ⟨posDef_of_inv hc₀ b1, b1, psd_mono ?_ b2, fun a b => ?_⟩
  · have h1 : R ≤ (1 + |M₀|) * r := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC.le
    nlinarith
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) (HodgeMetric.uncentre w₀ ρ π w) :=
      (GlobalTheory.T.period_gram_smooth_punctured n a₀ g _ Λ LP U hP.2.2.1 a b _ hu).comp _ (HodgeMetric.contDiff_uncentre 0 ρ' π').contDiffAt
    have h2 : (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) =ᶠ[nhds w]
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) ∘ HodgeMetric.uncentre w₀ ρ π := by
      filter_upwards [hev] with w' hw'
      rw [hw']
      rfl
    refine ⟨(h1.comp w (HodgeMetric.contDiff_uncentre w₀ ρ π).contDiffAt).congr_of_eventuallyEq h2, ?_⟩
    rw [h2.fderiv_eq, fderiv_comp w (h1.differentiableAt (by simp)) (hA w).differentiableAt, (hA w).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : Real.exp (R / 2) ≤ Real.exp (|M₀| / 2) * Real.exp (r / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 := (b3 a b).trans (mul_le_mul_of_nonneg_left h3 hC.le)
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg A)
    have h6 : 0 ≤ C * (1 + |M₀|) * Real.exp (r / 2) := by positivity
    nlinarith
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.flagModel_global_height_identity : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal <;> assumption)
end
end
