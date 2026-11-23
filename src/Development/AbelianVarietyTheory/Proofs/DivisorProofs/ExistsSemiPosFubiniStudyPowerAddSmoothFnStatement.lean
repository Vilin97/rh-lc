module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.ProjSpace
open scoped Matrix

namespace GlobalTheory.ProjPos

theorem leviV_log_pos {n N : ℕ} {w : Fin N → V n → ℂ} {x : V n} (hC : ∀ a, ContDiffAt ℂ 2 (w a) x) {j : Fin N}
    (hj : w j =ᶠ[𝓝 x] fun _ => 1) (ξ : V n) (h : ¬ ∀ a, fderiv ℂ (w a) x ξ = 0) :
    0 < (leviV n (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) x ξ.ofLp).re := by
  have hD : ∀ a, DifferentiableAt ℂ (w a) x := fun a => (hC a).differentiableAt (by simp)
  have h1 : w j x = 1 := hj.eq_of_nhds
  have hne : (fun i => w i x) ≠ 0 := fun e => one_ne_zero (h1.symm.trans (congrFun e j))
  have e1 : (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
  have hJ (a) : (wJac n N w x *ᵥ ξ.ofLp) a = fderiv ℂ (w a) x ξ := by
    have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
      ext i
      simp [bas, Pi.single_apply]
    conv_rhs => rw [hξ]

    simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hD a), map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, leviLogNormSq n N w x ξ.ofLp hC hne, Complex.ofReal_re]
  refine div_pos (sqNorm_pos fun hz => h fun a => ?_) (sqNorm_pos hne)
  rw [projPerp_mulVec, sub_eq_zero] at hz
  have h2 := congrFun hz j
  rw [hJ, hj.fderiv_eq, Pi.smul_apply, h1, smul_eq_mul, mul_one] at h2
  have h3 := congrFun hz a
  rw [hJ, ← h2] at h3
  simpa using h3

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {c : AlgChart p σ D} {y : CxPts p σ} {W : Y.Opens} {ξ : V D}


variable (c y ξ) in
def dirDer (f : Γ(Y, W)) : ℂ := fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) ξ

theorem dirDer_add (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f + g) = dirDer c y ξ f + dirDer c y ξ g := by
  have e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_add _ _ _
  simp only [dirDer, e, fderiv_add (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW)]
  rfl

theorem dirDer_mul (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f * g) = ev p σ W f y * dirDer c y ξ g + ev p σ W g y * dirDer c y ξ f := by
  have e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_mul _ _ _
  simp only [dirDer, e, fderiv_mul (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW),
    Function.comp_apply, c.e.left_inv hy]
  rfl

theorem dirDer_const (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) {f : Γ(Y, W)} {a : ℂ}
    (h : ∀ z ∈ ptsIn p σ W, ev p σ W f z = a) : dirDer c y ξ f = 0 := by
  have e : ev p σ W f ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => a :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun v hv => h _ hv.2
  rw [dirDer, e.fderiv_eq]
  simp

theorem dirDer_res {W' : Y.Opens} (h : W' ≤ W) (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W') (f : Γ(Y, W)) :
    dirDer c y ξ (resG Y h f) = dirDer c y ξ f := by
  have e : ev p σ W' (resG Y h f) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W f ∘ c.e.symm :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW))
      fun v hv => ev_res h hv.2 _
  simp only [dirDer, e.fderiv_eq]

theorem chartDirectionalDerivativeRegular_coordinate (hy : y ∈ c.e.source) (a : Fin D) : dirDer c y ξ (c.x a) = ξ a := by
  have e : ev p σ _ (c.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (EuclideanSpace.proj (𝕜 := ℂ) a : V D →L[ℂ] ℂ) :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv =>
      (c.apply_eq _ (c.e.map_target hv) a).symm.trans (by rw [c.e.right_inv hv]; rfl)
  rw [dirDer, e.fderiv_eq, ContinuousLinearMap.fderiv]
  rfl

theorem eq_zero_of_dirDer (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (hU : IsAffineOpen W)
    (h0 : ∀ f : Γ(Y, W), dirDer c y ξ f = 0) : ξ = 0 := by
  ext b
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := c.U) ⟨_, mem_ptsIn.1 (c.source_subset hy)⟩ (mem_ptsIn.1 hW)
  have hB : y ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW (c.x b))
  have ha' : resG Y hhW (c.x b) * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := by
    rw [map_pow]; exact ha
  have e := congrArg (dirDer c y ξ) ha'
  rw [dirDer_mul hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, h0, h0, chartDirectionalDerivativeRegular_coordinate hy, mul_zero,
    zero_add, ev_res _ hB, ev_eq hW, map_pow, ← ev_eq] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero n ((mem_ptsIn_basicOpen hW h).1 hB))

variable {N : ℕ} (i : Y ⟶ PSpace k N) (hi : i ≫ PSpace.str k N = p)


include hi in
theorem eq_zero_of_dirDer_ratio [IsClosedImmersion i] (hy : y ∈ c.e.source) {j : Fin (N + 1)}
    (hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j)) (h0 : ∀ a, dirDer c y ξ (i.app _ (ratio k N j a)) = 0) : ξ = 0 := by
  refine eq_zero_of_dirDer hy hW ((isAffineOpen_chart k N j).preimage i) fun f => ?_
  obtain ⟨g, rfl⟩ := i.app_surjective _ (isAffineOpen_chart k N j) f
  obtain ⟨P, rfl⟩ := aeval_ratio_surjective k N j g
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine dirDer_const hy hW (a := σ a) fun z hz => ?_
    rw [← ev_of_comp hm, MvPolynomial.aeval_C]
    exact ev_algX ((mem_ptsIn_preimage hm).1 hz) a
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), dirDer_add hy hW, hP, hQ, add_zero]
  | mul_X P a hP => rw [map_mul, map_mul, dirDer_mul hy hW, hP, MvPolynomial.aeval_X, h0, mul_zero, mul_zero, add_zero]

theorem fubiniStudy_weight_pullback_chart_formula (j : Fin (N + 1)) (z : CxPts p σ) :
    ((ProjAn.fsO1 k σ N).pull i hi).φ (fun _ => j) z =
      Real.log (∑ a, ‖ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) z‖ ^ 2) := by
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  refine (Weight.pull_φ _ _ _ _ _).trans ((Weight.fsBasis_φ _ _ _ _ _ _ _).trans
    (congrArg _ (Finset.sum_congr rfl fun a _ => ?_)))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← ev_of_comp hm]
  rfl

theorem fubiniStudy_weight_pullback_isSmooth (R : AnRead p σ D) : ((ProjAn.fsO1 k σ N).pull i hi).IsSmooth R :=
  Weight.IsSmooth.pull (R := .all _ σ N) (Weight.isSmooth_fsBasis _ _ _ _ _) i hi R

theorem fubiniStudy_weight_pullback_closed_immersion_strictPos [IsClosedImmersion i] (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull i hi).StrictPos R := by
  refine (fubiniStudy_weight_pullback_isSmooth i hi R).strictPos_of_exists fun y => ?_
  obtain ⟨l, hy⟩ := R.cover y
  obtain ⟨j, hj⟩ := exists_mem_chart k N (i (y.1 (IsLocalRing.closedPoint ℂ)))
  have hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j) := mem_ptsIn.2 hj
  set c := R.chart l
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (i ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (mem_over c.e hy hW)
  refine ⟨c, fun _ => j, hy, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => hj), fun ξ hξ => ?_⟩
  simp only [AlgChart.levi, fubiniStudy_weight_pullback_chart_formula]
  refine leviV_log_pos (w := fun a => ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) ∘ c.e.symm)
    (fun a => ((contDiffOn_of_differentiableOn D _ _ ho (c.holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)) (j := j) (eventually_of_mem hn fun v hv => ?_) (WithLp.toLp 2 ξ) fun h => ?_
  · rw [Function.comp_apply, ratio, ratioOn_self, map_one, ev_eq hv.2, map_one]
  · exact hξ (congrArg WithLp.ofLp (eq_zero_of_dirDer_ratio i hi hy hW h))

end GlobalTheory.ProjPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFn

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightShift

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem exists_semiPosReg_pow_addFn [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (R : AnRead p σ D) {φ : Weight p σ B} (h : φ.IsSmooth R) (hp : φ.StrictPos R)
    {v : CxPts p σ → ℝ} (hv : ∀ y, CInfAt v y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((φ.pow m).addFn v).SemiPosReg D := by
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hv' : R.SmoothOn univ v := (cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y
  have hw : R.finAtlas.Smooth fun y => v y / 2 :=
    (hA.smooth_iff R).2 fun c => (hv' c).div_const 2
  have hΩ := h.isPotential hA
  have hpos := (h.isPosPot_iff hA).2 hp
  have hpsh : IsPsh R.finAtlas φ.locPot := fun x j z hz w => by
    by_cases h0 : w = 0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (hpos x j z hz w h0).le
  obtain ⟨C, hC⟩ := pshShift R.finAtlas φ.locPot hΩ hpos _ hw
  refine ⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩
  have hmC : 0 ≤ (m : ℝ) - C := sub_nonneg.2 (Nat.ceil_le.1 hm)
  have hχ : ((φ.pow m).addFn v).IsSmooth R := (h.zpow m).addFn hv'
  obtain ⟨j, hj⟩ := R.finAtlas.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  have hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y) :=
    mem_pow_iff.2 (mem_pick φ.isLB y)
  obtain ⟨w, -, e⟩ := hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ
  rw [hχ.leviV_re_eq c hy.1 hy.2, e]
  have hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y :=
    mem_over c'.e hj (φ.locPot.mem_U y)
  have h₁ := hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w
  have h₂ := hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w
  rw [hc'] at h₁ h₂
  have d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm)
      (c'.finChart y) := hχ.contDiffAt_finChart c' hj hb
  have d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y) :=
    (h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2
  have e₁ := ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂
  rw [FinChart.levi_half] at e₁
  have e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm =
      fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 +
        (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z := by
    funext z
    have := φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)
    change v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) =
      ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 +
        (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)
    rw [this]
    push_cast
    ring
  rw [e₂, e₁] at h₁
  nlinarith [mul_nonneg hmC h₂]

theorem strictPos_fsO1 (N : ℕ) (R : AnRead (PSpace.str k N) σ N) :
    (ProjAn.fsO1 k σ N).StrictPos R := fun i c y hy ξ h0 => by
  have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R
    (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0
  have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PSpace.str k N))).φ (fun _ => i) z =
      (ProjAn.fsO1 k σ N).φ i z := by
    refine (Weight.pull_φ _ _ _ _ _).trans ?_
    have e : PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str k N)) _ z = z :=
      Subtype.ext (Category.comp_id _)
    erw [e]
  simpa only [e] using this

theorem exists_semiPosReg_fubiniStudy : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := fun k _ σ N v hv =>
  haveI : T2Space (CxPts (PSpace.str k N) σ) :=
    CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exists_semiPosReg_pow_addFn (AnRead.all _ σ N)
    ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv

end GlobalTheory.WeightShift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFnStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := by
  first | exact @GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | exact GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | (intros; apply GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy <;> assumption)
end
end
