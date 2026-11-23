module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniformStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPartPosDefLogDetBoundOfConjugateComparableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConjStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.sectionValueUnitFrame_conj_point_eq_phase_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  first | exact @GlobalTheory.HSAmp.val_conj | exact GlobalTheory.HSAmp.val_conj | (intros; apply GlobalTheory.HSAmp.val_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDet

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BallGram

def comb {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) : (Fin r → ℤ) →+ K :=
  AddMonoidHom.mk' (fun z => ∑ i, z i • f i) fun z w => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem comb_apply {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (z : Fin r → ℤ) :
    comb f z = ∑ i, z i • f i := rfl

theorem mem_closure_iff {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (g : K) :
    g ∈ AddSubgroup.closure (Set.range f) ↔ ∃ z, comb f z = g := by
  constructor
  · intro hg
    have hle : AddSubgroup.closure (Set.range f) ≤ (comb f).range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_⟩
      simp [comb_apply, Pi.single_apply]
    exact hle hg
  · rintro ⟨z, rfl⟩
    rw [comb_apply]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

theorem comb_injective {K : Type} [AddCommGroup K] {r : ℕ} (f : Fin r → K) (hf : LinearIndependent ℤ f) :
    Function.Injective (comb f) :=
  (injective_iff_map_eq_zero (comb f)).2 fun z hz => funext (Fintype.linearIndependent_iff.1 hf z hz)

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem val_comb (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (σ : k →+* ℂ) (y : CxPts p σ) (z : Fin r → ℤ) :
    val P a b σ y (comb f z) = ∑ i, (z i : ℂ) * val P a b σ y (f i) := by
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y
  have hmem : comb f z ∈ P.H a b := by
    rw [comb_apply]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hf i) _
  have heq : (⟨comb f z, hmem⟩ : P.H a b) = ∑ i, z i • (⟨f i, hf i⟩ : P.H a b) := by
    apply Subtype.ext
    simp [comb_apply]

  rw [← hℓ ⟨comb f z, hmem⟩, heq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hℓ, zsmul_eq_mul]

theorem nu_comb_sq (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (σ : k →+* ℂ) (y : CxPts p σ) (z : Fin r → ℤ) :
    P.nu a b σ y (comb f z) ^ 2 = cmb (vals P a b f) (fun i => (z i : ℂ)) σ y := by
  rw [← norm_val, val_comb P a b f hf, cmb]
  rfl

theorem jacobi_field_square_integrable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {r : ℕ} (μ : ∀ σ, Measure (Y σ))
    (v : ∀ σ, Y σ → Fin r → ℂ) (h : IsFam μ v) (z : Fin r → ℤ) :
    l2 μ v (fun i => (z i : ℂ)) = ∑ i, ∑ j, (gram μ v).map Complex.re i j * (z i : ℝ) * (z j : ℝ) := by
  have h1 := congrArg Complex.re ((gram_isHermitian_and_l2_eq_quadratic_form S Y (Fin r) μ v h).2 (fun i => (z i : ℂ))).2.2
  rw [Complex.ofReal_re] at h1
  rw [h1, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_intCast, Matrix.map_apply]
  simp [Complex.mul_re]
  ring

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem cmb_conj_le (P : Pair p) (a b : ℤ) {r : ℕ} (f : Fin r → X.functionField) (hf : ∀ i, f i ∈ P.H a b)
    (c : Fin r → ℂ) (B : ℝ) (hB : ∀ σ y, cmb (vals P a b f) c σ y ≤ B) (σ : k →+* ℂ) (y : CxPts p σ) :
    cmb (vals P a b f) (fun i => starRingEnd ℂ (c i)) σ y ≤ B := by
  obtain ⟨σ', y', θ, hθ, hval⟩ := GlobalTheory.T.sectionValueUnitFrame_conj_point_eq_phase_conj k X p P a b σ y
  refine le_trans (le_of_eq ?_) (hB σ' y')
  simp only [cmb, vals]
  have h : ∑ i, c i * val P a b σ' y' (f i) =
      θ * starRingEnd ℂ (∑ i, starRingEnd ℂ (c i) * val P a b σ y (f i)) := by

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval _ (hf i), map_mul, Complex.conj_conj]
    ring
  rw [h, norm_mul, hθ, one_mul, Complex.norm_conj]

end GlobalTheory.BallGram

namespace GlobalTheory.BallGram

theorem count_ball_gram : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ (M Vv ρ R : ℝ), 1 ≤ M → 1 ≤ Vv → (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) ≤ Vv → 0 ≤ ρ → 0 < R → (∀ (c : Fin r → ℂ) σ y, cmb (vals P a b f) c σ y ≤ M * l2 (fun σ => (ω σ).meas) (vals P a b f) c) → AddSubgroup.closure (Set.range f) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range f)) a b ρ) → 2 * r * ρ * (M * Vv) ≤ R → |Real.log ((ballIn P (AddSubgroup.closure (Set.range f)) a b R).ncard : ℝ) - (r * Real.log R - Real.log (gram (fun σ => (ω σ).meas) (vals P a b f)).det.re / 2 + Real.log (volume {x : Fin r → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ 2 * r * Real.log (2 * (M * Vv)) := by
  intro k _ X _ p D hX hS P ω a b r f hf hli M Vv ρ R hM hV hvol hρ hR hsup hgen hRρ
  obtain ⟨hfam, hpd, hbd⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hS P ω a b (Fin r) f hf hli
  have hl2 := (gram_isHermitian_and_l2_eq_quadratic_form _ _ (Fin r) _ _ hfam).2
  set μ : ∀ σ, Measure (CxPts p σ) := fun σ => (ω σ).meas with hμ
  set v := vals P a b f with hv
  set G := gram μ v with hG
  set A := G.map Complex.re with hA
  set Λ := AddSubgroup.closure (Set.range f) with hΛ
  set φ := comb f with hφ
  have hinj : Function.Injective φ := comb_injective f hli
  set Q : (Fin r → ℤ) → ℝ := fun z => ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) with hQ
  have hQl2 : ∀ z, l2 μ v (fun i => (z i : ℂ)) = Q z := fun z => jacobi_field_square_integrable μ v hfam z
  have hnu0 : ∀ σ y g, 0 ≤ P.nu a b σ y g := fun σ y g => by rw [← norm_val]; exact norm_nonneg _
  have hM0 : 0 < M := by linarith
  have hV0 : 0 < Vv := by linarith
  have hin : ∀ z (R' : ℝ), 0 ≤ R' → Q z ≤ R' ^ 2 / M → φ z ∈ ballIn P Λ a b R' := by
    intro z R' hR' hz
    refine ⟨(mem_closure_iff f _).2 ⟨z, rfl⟩, fun σ y => ?_⟩
    have h1 : P.nu a b σ y (φ z) ^ 2 ≤ R' ^ 2 := by
      rw [nu_comb_sq P a b f hf]
      calc cmb v (fun i => (z i : ℂ)) σ y ≤ M * l2 μ v (fun i => (z i : ℂ)) := hsup _ σ y
        _ = M * Q z := by rw [hQl2]
        _ ≤ M * (R' ^ 2 / M) := mul_le_mul_of_nonneg_left hz hM0.le
        _ = R' ^ 2 := by field_simp
    exact (pow_le_pow_iff_left₀ (hnu0 σ y _) hR' two_ne_zero).1 h1
  have hout : ∀ z (R' : ℝ), φ z ∈ ballIn P Λ a b R' → Q z ≤ Vv * R' ^ 2 := by
    intro z R' hz
    have h1 : ∀ σ y, cmb v (fun i => (z i : ℂ)) σ y ≤ R' ^ 2 := fun σ y => by
      rw [← nu_comb_sq P a b f hf]
      exact pow_le_pow_left₀ (hnu0 σ y _) (hz.2 σ y) 2
    rw [← hQl2]
    calc l2 μ v (fun i => (z i : ℂ)) ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * R' ^ 2 := hbd _ _ h1
      _ ≤ Vv * R' ^ 2 := mul_le_mul_of_nonneg_right hvol (sq_nonneg _)
  have himg : ∀ R', ballIn P Λ a b R' = φ '' {z | φ z ∈ ballIn P Λ a b R'} := by
    intro R'
    ext g
    constructor
    · intro hg
      obtain ⟨z, rfl⟩ := (mem_closure_iff f g).1 hg.1
      exact ⟨z, hg, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  have hcard : ∀ R', (ballIn P Λ a b R').ncard = {z | φ z ∈ ballIn P Λ a b R'}.ncard := fun R' =>
    (congrArg Set.ncard (himg R')).trans (Set.ncard_image_of_injective _ hinj)
  set T := {z | φ z ∈ ballIn P Λ a b ρ} with hT
  have hTtop : AddSubgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have h1 : φ z ∈ Λ := (mem_closure_iff f _).2 ⟨z, rfl⟩
    have h2 := hgen h1
    rw [himg ρ, ← AddMonoidHom.map_closure] at h2
    obtain ⟨w, hw, hwz⟩ := h2
    rwa [hinj hwz] at hw
  have hTQ : ∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ (ρ * √Vv) ^ 2 := fun z hz => by
    rw [mul_pow, Real.sq_sqrt hV0.le]
    have := hout z ρ hz
    simp only [hQ] at this
    linarith
  have hκ : 1 ≤ M * Vv := one_le_mul_of_one_le_of_one_le hM hV
  have hcomp : ∀ c : Fin r → ℂ, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * G i j).re ≤
      (M * Vv) * (∑ i, ∑ j, c i * starRingEnd ℂ (c j) * G i j).re := by
    intro c
    have e1 := (hl2 (fun i => starRingEnd ℂ (c i))).2.2
    simp only [Complex.conj_conj] at e1
    rw [← e1, ← (hl2 c).2.2, Complex.ofReal_re, Complex.ofReal_re]
    have h0 := (hl2 c).2.1
    calc l2 μ v (fun i => starRingEnd ℂ (c i)) ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * (M * l2 μ v c) :=
          hbd _ _ (cmb_conj_le P a b f hf c _ (hsup c))
      _ ≤ Vv * (M * l2 μ v c) := mul_le_mul_of_nonneg_right hvol (mul_nonneg hM0.le h0)
      _ = M * Vv * l2 μ v c := by ring
  obtain ⟨hApd, hdet⟩ := GlobalTheory.T.realPart_posDef_logDet_bound_of_conjugate_comparable (Fin r) G (M * Vv) hpd hκ hcomp
  have hsM : 0 < √M := Real.sqrt_pos.2 hM0
  have hsV : 0 < √Vv := Real.sqrt_pos.2 hV0
  set R1 := R / √M with hR1d
  set R2 := R * √Vv with hR2d
  have hR1 : 0 < R1 := div_pos hR hsM
  have hR2 : 0 < R2 := mul_pos hR hsV
  have hρ' : 0 ≤ ρ * √Vv := mul_nonneg hρ hsV.le
  have hcardr : (Fintype.card (Fin r) : ℝ) = r := by simp
  have hsq : √M * √Vv ≤ M * Vv := by
    rw [← Real.sqrt_mul hM0.le]
    calc √(M * Vv) ≤ √(M * Vv) * √(M * Vv) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr hκ)
      _ = M * Vv := Real.mul_self_sqrt (by positivity)
  have h2rρ : 0 ≤ 2 * (r : ℝ) * ρ := by positivity
  have hb1 : 2 * (Fintype.card (Fin r) : ℝ) * (ρ * √Vv) ≤ R1 := by
    rw [hcardr, hR1d, le_div_iff₀ hsM]
    calc 2 * (r : ℝ) * (ρ * √Vv) * √M = 2 * r * ρ * (√M * √Vv) := by ring
      _ ≤ 2 * r * ρ * (M * Vv) := mul_le_mul_of_nonneg_left hsq h2rρ
      _ ≤ R := hRρ
  have hb2 : 2 * (Fintype.card (Fin r) : ℝ) * (ρ * √Vv) ≤ R2 := by
    rw [hcardr, hR2d]
    calc 2 * (r : ℝ) * (ρ * √Vv) = (2 * r * ρ) * √Vv := by ring
      _ ≤ R * √Vv := mul_le_mul_of_nonneg_right (le_trans (le_mul_of_one_le_right h2rρ hκ) hRρ) hsV.le
  have c1 := GlobalTheory.T.log_lattice_points_quadratic_ball_estimate (Fin r) A hApd T (ρ * √Vv) R1 hρ' hR1 hTtop hTQ hb1
  have c2 := GlobalTheory.T.log_lattice_points_quadratic_ball_estimate (Fin r) A hApd T (ρ * √Vv) R2 hρ' hR2 hTtop hTQ hb2
  set B := {z | φ z ∈ ballIn P Λ a b R} with hB
  have hsub1 : {z : Fin r → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R1 ^ 2} ⊆ B := fun z hz => by
    refine hin z R hR.le ?_
    have hz' : ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R1 ^ 2 := hz
    rw [hR1d, div_pow, Real.sq_sqrt hM0.le] at hz'
    exact hz'
  have hsub2 : B ⊆ {z : Fin r → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R2 ^ 2} := fun z hz => by
    show ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R2 ^ 2
    rw [hR2d, mul_pow, Real.sq_sqrt hV0.le]
    have := hout z R hz
    simp only [hQ] at this
    linarith
  have hfin : B.Finite := c2.1.subset hsub2
  have hn1 : ellCount A R1 ≤ B.ncard := Set.ncard_le_ncard hsub1 hfin
  have hn2 : B.ncard ≤ ellCount A R2 := Set.ncard_le_ncard hsub2 c2.1
  have hpos : 0 < ellCount A R1 := (Set.ncard_pos c1.1).2 ⟨0, by simp; positivity⟩
  rw [hcard R]
  have l1 : Real.log (ellCount A R1) ≤ Real.log B.ncard :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hn1)
  have l2' : Real.log B.ncard ≤ Real.log (ellCount A R2) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le hpos hn1)) (by exact_mod_cast hn2)
  have lr1 : Real.log R1 = Real.log R - Real.log M / 2 := by
    rw [hR1d, Real.log_div hR.ne' hsM.ne', Real.log_sqrt hM0.le]
  have lr2 : Real.log R2 = Real.log R + Real.log Vv / 2 := by
    rw [hR2d, Real.log_mul hR.ne' hsV.ne', Real.log_sqrt hV0.le]
  have c1b := c1.2
  have c2b := c2.2
  rw [hcardr, lr1] at c1b
  rw [hcardr, lr2] at c2b
  rw [hcardr] at hdet
  have hx : M * Vv ≤ 2 * (M * Vv) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hlM : Real.log M ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log hM0 ((le_mul_of_one_le_right hM0.le hV).trans hx)
  have hlV : Real.log Vv ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log hV0 ((le_mul_of_one_le_left hV0.le hM).trans hx)
  have hlt : Real.log 2 ≤ Real.log (2 * (M * Vv)) :=
    Real.log_le_log (by norm_num) (le_mul_of_one_le_right (by norm_num) hκ)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have m1 := mul_le_mul_of_nonneg_left hlM hr0
  have m2 := mul_le_mul_of_nonneg_left hlV hr0
  have m3 := mul_le_mul_of_nonneg_left hlt hr0
  obtain ⟨c1x, c1y⟩ := abs_le.1 c1b
  obtain ⟨c2x, c2y⟩ := abs_le.1 c2b
  obtain ⟨dx, dy⟩ := abs_le.1 hdet
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.BallGram
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDetStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ (M Vv ρ R : ℝ), 1 ≤ M → 1 ≤ Vv → (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) ≤ Vv → 0 ≤ ρ → 0 < R → (∀ (c : Fin r → ℂ) σ y, cmb (vals P a b f) c σ y ≤ M * l2 (fun σ => (ω σ).meas) (vals P a b f) c) → AddSubgroup.closure (Set.range f) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range f)) a b ρ) → 2 * r * ρ * (M * Vv) ≤ R → |Real.log ((ballIn P (AddSubgroup.closure (Set.range f)) a b R).ncard : ℝ) - (r * Real.log R - Real.log (gram (fun σ => (ω σ).meas) (vals P a b f)).det.re / 2 + Real.log (volume {x : Fin r → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ 2 * r * Real.log (2 * (M * Vv)) := by
  first | exact @GlobalTheory.BallGram.count_ball_gram | exact GlobalTheory.BallGram.count_ball_gram | (intros; apply GlobalTheory.BallGram.count_ball_gram <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminant

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have h0 : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ h0).1 hm).le
  have hexp := eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m) := by
      calc 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V)
          ≤ 2 * ((g + 1) * (m : ℝ) ^ D) * C ^ m * (K * (m : ℝ) ^ D * V) := by
            have : 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V) := by
              have : 0 ≤ C := by linarith
              positivity
            nlinarith
        _ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring
        _ ≤ _ := hem
    have key := GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m)
      (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR
    rw [Real.log_exp] at key
    have hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m := by
      have e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D := by ring
      rw [e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]
    have hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans (le_of_eq ?_)
    rw [hlog, pow_succ]
    field_simp
  · have h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g)) := hg.const_mul 2
    have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using h1.mul h2

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminantStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.HSAmp.count_ball_asymp | exact GlobalTheory.HSAmp.count_ball_asymp | (intros; apply GlobalTheory.HSAmp.count_ball_asymp <;> assumption)
end
end
