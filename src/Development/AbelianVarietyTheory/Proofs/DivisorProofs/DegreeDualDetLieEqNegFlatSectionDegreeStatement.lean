module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPo
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInvStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet

section

@[expose] public section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.DefPt.ArchVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_homN_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : G.2 = 0) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exZ Dw G)) {Z : Comp Xo c} {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ}
    (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    ∃ z ∈ framesOn U Z, homN U ξ G f z = ‖toC (evR Xo c f y)‖ := by
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r U hU y
  refine ⟨⟨k, x.1⟩, ⟨x.2, liesOn_frBor ht hy⟩, ?_⟩
  obtain ⟨g, hg0, hgd, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k x (hξ k) hx
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨-, hGr⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      ‖toC (t (some p) : CAt σ)‖ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
    rintro ⟨τ, i⟩
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    rw [← hgd τ i, ← hs]
    exact GlobalTheory.LamT.OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hGr τ).symm i
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hev := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ hf (CAt σ) t _ _ ht
  have hw : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = lieFacZ Dw ξ G := by
    have e : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = ∏ i, ‖toC (t i : CAt σ)‖ ^ exZ Dw G i := by
      show ‖((∏ i, (show Ix Dw → ℂˣ from t) i ^ exZ Dw G i : ℂˣ) : ℂ)‖ = _
      rw [Units.coe_prod, norm_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, norm_zpow]; rfl
    rw [e, Fintype.prod_option]
    simp only [hsome, exZ, hG, zpow_zero, one_mul, ← Real.rpow_intCast, ← Real.exp_mul]
    rw [← Real.exp_sum, lieFacZ, ← Finset.mul_sum, Fintype.sum_sigma]
    congr 1; ring
  have hrd : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
  rw [homN, ptN, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hx),
    hev, ← hw]
  show _ * ‖rdU U f k x.1‖ = _
  rw [hrd]
  exact (norm_mul (toC _) (toC _)).symm

theorem cInf_eq {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U ξ Z la δ) {σ : c.F →+* ℂ}
    {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ} (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    s.cInf σ = ‖toC (evR Xo c s.sig y)‖ := by
  have key : ∀ σ' : c.F →+* ℂ, goodOf c σ = σ' → ∀ y' : FrPt Xo c (CAt σ'), LiesOn Z y' →
      (GlobalTheory.LamT.IsMetric y' N fun _ => 1) → s.cInf σ = ‖toC (evR Xo c s.sig y')‖ := by
    rintro _ rfl y' hy' hN'
    have hg := goodEmb_goodOf c σ
    obtain ⟨z, hz, e⟩ := exists_homN_eq (U _) hg (hU _ hg) (hξ _ hg) hpq (G := wtOf Dw la 0) rfl s.sig_mem hy' hN'
    rw [← e, s.homN_eq hz]
  by_cases hσ : GoodEmb c σ
  · exact key σ (if_pos hσ) y hy hN
  · have hB := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hN
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 s.sig s.sig_mem.1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [key _ (if_neg hσ) y' (liesOn_frMap hy' hy) hm', hev]
    exact Complex.norm_conj _

theorem cInf_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b _ hb σ
  obtain ⟨-, hX, hA⟩ := P.arch σ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId c.F (CAt σ)) P.y₀
  have hu : ∀ τ', IsUnit (M := ℂ) (P.X σ τ').det := fun τ' => (hX τ').isUnit
  obtain ⟨y, hy⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (CAt σ) (fun τ' => (P.X σ τ')ᵀ) 1 z).1
    (fun τ' => show IsUnit (M := ℂ) ((P.X σ τ')ᵀ).det from (Matrix.det_transpose (P.X σ τ')).symm ▸ hu τ') isUnit_one
  have hon : LiesOn Z y := fun q => by
    have e : ptF y = ptF z := by
      apply Limits.pullback.hom_ext
      · rw [ptF, Limits.pullback.lift_fst, ptF, Limits.pullback.lift_fst, hy.1]
      · rw [ptF, Limits.pullback.lift_snd, ptF, Limits.pullback.lift_snd]
    rw [e]
    exact liesOn_frMap hz P.on q
  have h : toC (evR Xo c s.sig y) * (P.X σ τ.1).det = σ b := hb (CAt σ) z y (P.X σ) 1 hu isUnit_one hz hy
  rw [cInf_eq hD.unf hD.xi (hD.p.trans (Nat.le_add_right _ _)) s hon (hA z y hz hy), ← h, norm_mul,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hX τ.1))]

end GlobalTheory.DefPt.ArchVal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDetStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  first | exact @GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | exact GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | (intros; apply GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDet

section

@[expose] public section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem vV_algebraMap_of_isUnit (T : CDVR) {u : T.V} (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem rho_vw_eq_vAdd_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b hb hev w
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  have hval := s.val_eq hv
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  have hval' : nval T.V e (evR Xo c s.sig y.1) = ((flDefect_vw Dw c τ w + s.rho_vw w : ℝ) : EReal) := hval
  have hδ : flDefect_vw Dw c τ w = 0 := by simp [flDefect_vw, hD.q]
  rw [hδ, zero_add] at hval'
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F T.Fr
    (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hloc⟩ := P.loc w
  have hx : y.1.x = z.x := (P.only T.Fr y.1 hy.2).trans hz.1.symm
  obtain ⟨Y, u, hY, hch⟩ := hloc T io e ho y.1 z y.2.2 hz hx
  have hdet : ∀ τ', ((P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)).det =
      io (P.B w τ').det * algebraMap T.V T.Fr (Y τ').det := fun τ' => by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hYne : ∀ τ', algebraMap T.V T.Fr (Y τ').det ≠ 0 := fun τ' => ((hY τ').map _).ne_zero
  have hBne : ∀ τ', io (P.B w τ').det ≠ 0 := fun τ' => (map_ne_zero io).2 (hB τ')
  have key := hev T.Fr z y.1 (fun τ' => (P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)) _
    (fun τ' => by rw [hdet]; exact (mul_ne_zero (hBne τ') (hYne τ')).isUnit)
    (mul_ne_zero ((map_ne_zero io).2 ha) (u.isUnit.map _).ne_zero).isUnit hz hch
  rw [hdet] at key
  have key' : evR Xo c s.sig y.1 * (io (P.B w τ.1).det * algebraMap T.V T.Fr (Y τ.1).det) = io b := key
  have hbne : io b ≠ 0 := (map_ne_zero io).2 hb
  have h0 : evR Xo c s.sig y.1 ≠ 0 := left_ne_zero_of_mul (key' ▸ hbne)
  have h1 := congrArg (vV T.V) key'
  rw [vV_mul h0 (mul_ne_zero (hBne _) (hYne _)), vV_mul (hBne _) (hYne _), vV_algebraMap_of_isUnit T (hY _),
    ho.2, ho.2] at h1
  rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at hval'
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  rw [← hval', div_eq_iff he]
  show _ = ((vLa w b : ℝ) - (vLa w (P.B w τ.1).det : ℝ)) * e
  linarith

end GlobalTheory.DefPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDetStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  first | exact @GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | exact GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | (intros; apply GlobalTheory.DefPt.rho_vw_eq_vAdd_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree

section

@[expose] public section

noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem degLie_eq_neg_deg_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P
  refine ⟨fun τ s => ?_, fun τ h => ?_⟩
  · obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_flatSectionValue_eq_mul_det_inv E H Dw l Xo c r U ξ hD Z P τ s
    have h2 := GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have h3 := GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det E H Dw l Xo c r U ξ hD Z P τ s b hb0 hb
    have hX : ∀ σ, 0 < ‖(P.X σ τ.1).det‖ := fun σ => norm_pos_iff.2 ((P.arch σ).2.1 τ.1)
    have hfB : (Function.support fun w => (vAdd w (P.B w τ.1).det : ℝ)).Finite := by
      have e : (fun w => (vAdd w (P.B w τ.1).det : ℝ)) = (fun w => (vAdd w b : ℝ)) - s.rho_vw := by
        funext w; rw [Pi.sub_apply, h2 w]; ring
      rw [e]
      exact ((finite_vAdd hb0).union s.finite_rho).subset (Function.support_sub _ _)
    have hm := lineDeg_mul (r := fun σ => ‖(P.X σ τ.1).det‖) (r' := s.cInf) hX s.cInf_pos hfB s.finite_rho
    have e1 : ((fun σ => ‖(P.X σ τ.1).det‖) * s.cInf) = fun σ : c.F →+* ℂ => ‖σ b‖ := by
      funext σ; rw [Pi.mul_apply, h3 σ]; field_simp [(hX σ).ne']
    have e2 : ((fun w => (vAdd w (P.B w τ.1).det : ℝ)) + s.rho_vw) = fun w => (vAdd w b : ℝ) := by
      funext w; rw [Pi.add_apply, h2 w]; ring
    rw [e1, e2, lineDeg_num hb0] at hm
    have : P.degLie τ.1 + s.deg = 0 := by
      rw [hm]; rfl
    linarith
  · have hq : Dw.q = 0 := hD.q
    simp only [Datum.mult, if_neg h, hq]

end GlobalTheory.DefPt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegreeStatement

section

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  first | exact @GlobalTheory.DefPt.degLie_eq_neg_deg_flat | exact GlobalTheory.DefPt.degLie_eq_neg_deg_flat | (intros; apply GlobalTheory.DefPt.degLie_eq_neg_deg_flat <;> assumption)
end
end
