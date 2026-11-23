module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendAeLinearOfLocalSqBoundDenseStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AeEqOfDenseOfLocalSqBound

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem ae_eq_of_dense_of_local_sq_bound : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  intro X _ μ K _hK hcov H _ _ E _ _ D hD P Q hP hQ hPb hQb hPQ u
  have key : ∀ n, ∀ᵐ x ∂μ.restrict (K n), P u x = Q u x := by
    intro n
    obtain ⟨CP, hCP⟩ := hPb n
    obtain ⟨CQ, hCQ⟩ := hQb n
    have hmeas : AEMeasurable (fun x => ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2) (μ.restrict (K n)) :=
      (((hCP u).1.sub (hCQ u).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2
    set M : ℝ := 2 * (|CP| + |CQ|) with hM
    have hbound : ∀ δ : ℝ, 0 < δ →
        ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) ≤ ENNReal.ofReal (M * δ ^ 2) := by
      intro δ hδ
      obtain ⟨u', hu'D, hdist⟩ := hD.exists_dist_lt u hδ
      have hwδ : ‖u - u'‖ ^ 2 ≤ δ ^ 2 := by
        have : ‖u - u'‖ < δ := by rw [← dist_eq_norm]; exact hdist
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      have hae : ∀ᵐ x ∂(μ.restrict (K n)), ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ≤
          2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 := by
        have h1 := ae_restrict_of_ae (s := K n) (hP u u')
        have h2 := ae_restrict_of_ae (s := K n) (hQ u u')
        have h3 := ae_restrict_of_ae (s := K n) (hPQ u' hu'D)
        filter_upwards [h1, h2, h3] with x e1 e2 e3
        have e1' : P u x - P u' x = P (u - u') x := e1
        have e2' : Q u x - Q u' x = Q (u - u') x := e2
        have e3' : P u' x = Q u' x := e3
        have e : P u x - Q u x = P (u - u') x - Q (u - u') x := by
          have : P u x - Q u x = (P u x - P u' x) - (Q u x - Q u' x) + (P u' x - Q u' x) := by abel
          rw [this, e1', e2', e3', sub_self, add_zero]
        rw [e]
        have hn : ‖P (u - u') x - Q (u - u') x‖₊ ≤ ‖P (u - u') x‖₊ + ‖Q (u - u') x‖₊ := nnnorm_sub_le _ _
        have hsq : ‖P (u - u') x - Q (u - u') x‖₊ ^ 2 ≤
            2 * ‖P (u - u') x‖₊ ^ 2 + 2 * ‖Q (u - u') x‖₊ ^ 2 := by
          have hn' : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ≤
              ((‖P (u - u') x‖₊ : NNReal) : ℝ) + ((‖Q (u - u') x‖₊ : NNReal) : ℝ) := by exact_mod_cast hn
          have h0 : (0:ℝ) ≤ ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) := NNReal.coe_nonneg _
          have hreal : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 ≤
              2 * ((‖P (u - u') x‖₊ : NNReal) : ℝ) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (((‖P (u - u') x‖₊ : NNReal) : ℝ) - ((‖Q (u - u') x‖₊ : NNReal) : ℝ))]
          exact_mod_cast hreal
        have := ENNReal.coe_le_coe.mpr hsq
        push_cast at this
        exact this
      calc ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n))
          ≤ ∫⁻ x, (2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2)
              ∂(μ.restrict (K n)) := lintegral_mono_ae hae
        _ = 2 * ∫⁻ x, ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) +
              2 * ∫⁻ x, ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) := by
            rw [lintegral_add_left'
              (((hCP (u - u')).1.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2).const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * ENNReal.ofReal (CP * ‖u - u'‖ ^ 2) + 2 * ENNReal.ofReal (CQ * ‖u - u'‖ ^ 2) := by
            gcongr
            · exact (hCP (u - u')).2
            · exact (hCQ (u - u')).2
        _ ≤ 2 * ENNReal.ofReal (|CP| * δ ^ 2) + 2 * ENNReal.ofReal (|CQ| * δ ^ 2) := by
            gcongr <;> first | exact le_abs_self _ | exact hwδ
        _ = ENNReal.ofReal (M * δ ^ 2) := by
            have : M * δ ^ 2 = 2 * (|CP| * δ ^ 2) + 2 * (|CQ| * δ ^ 2) := by rw [hM]; ring
            rw [this, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    have hzero : ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) = 0 := by
      have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (M * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (ENNReal.ofReal (M * 0 ^ 2))) := by
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        exact (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))).tendsto 0
      have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hbound δ hδ))
      simpa using this
    have hae0 := (lintegral_eq_zero_iff' hmeas).mp hzero
    filter_upwards [hae0] with x hx
    have hx' : ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 = 0 := hx
    simpa [sub_eq_zero] using hx'
  have hall : ∀ᵐ x ∂μ.restrict (⋃ n, K n), P u x = Q u x :=
    (ae_restrict_iUnion_iff K (fun x => P u x = Q u x)).mpr key
  rw [hcov, Measure.restrict_univ] at hall
  exact hall

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AeEqOfDenseOfLocalSqBoundStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  first | exact @GlobalTheory.ae_eq_of_dense_of_local_sq_bound | exact GlobalTheory.ae_eq_of_dense_of_local_sq_bound | (intros; apply GlobalTheory.ae_eq_of_dense_of_local_sq_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMatrixCoeffExtendsBoundedEquivariant

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
  {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a : ℝ} {μG : Measure (Mt k r)} {d : ℝ}
  {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}

theorem afun_add (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u u' : H} (hu : u ∈ DD σ w) (hu' : u' ∈ DD σ w) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (u + u') v ξ x =
      Afun (psiGen k r z c) π μS σ u v ξ x + Afun (psiGen k r z c) π μS σ u' v ξ x := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).1
  have h2 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u') (hst x hx u' hu') v hv).1
  simp only [Afun, be, map_add (f := _), coef_add_left, add_smul]
  rw [integral_add h1 h2, ContinuousLinearMap.add_apply]

theorem afun_smul (b : ℂ) (u v : H) (ξ : Wp) (x : Mat k r) :
    Afun (psiGen k r z c) π μS σ (b • u) v ξ x = b • Afun (psiGen k r z c) π μS σ u v ξ x := by
  simp only [Afun, be, map_smul, coef_smul_left, mul_smul]
  rw [integral_smul, ContinuousLinearMap.smul_apply]

theorem afun_mul_right (hσ : IsURepOn (GG k r) σ) (u v : H) (ξ : Wp) {x y : Mat k r}
    (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (σ y u) v ξ x = Afun (psiGen k r z c) π μS σ u v ξ (x * y) := by
  simp only [Afun, hσ.1.2 x hx y hy, ContinuousLinearMap.comp_apply]

theorem afun_mul_left (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u : H} (hu : u ∈ DD σ w) {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r)
    (hSG : Sset k r z ⊆ GG k r) :
    Afun (psiGen k r z c) π μS σ u v ξ (s * x) =
      PiS (psiGen k r z c) π s (Afun (psiGen k r z c) π μS σ u v ξ x) := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h := ((GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).2.1 s hs).1
  simp only [Afun]
  rw [hStd.2.1.1.2 s (hSG hs) x hx, ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.comp_apply]

theorem continuous_lmulM' (s : Mat k r) : Continuous (lmulM s : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem lintegral_comp_le_image {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] {μ : Measure X} {φ : X → X} (hmp : MeasurePreserving φ μ μ) (hφ : Continuous φ)
    (f : X → ENNReal) {K : Set X} (hK : IsCompact K) (hf : AEMeasurable f μ) :
    ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x in φ '' K, f x ∂μ := by
  have hm : MeasurableSet (φ '' K) := (hK.image hφ).isClosed.measurableSet
  have hmap : μ.map φ = μ := hmp.map_eq
  calc ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x, (φ '' K).indicator f (φ x) ∂μ := by
        rw [← lintegral_indicator hK.isClosed.measurableSet]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [Set.indicator, hx, Set.mem_image_of_mem φ hx]
        · simp [Set.indicator, hx]
    _ = ∫⁻ y, (φ '' K).indicator f y ∂μ := by
        have := lintegral_map' (μ := μ) (f := (φ '' K).indicator f) (g := φ)
          (by rw [hmap]; exact hf.indicator hm) hφ.aemeasurable
        rw [hmap] at this
        exact this.symm
    _ = ∫⁻ y in φ '' K, f y ∂μ := lintegral_indicator hm _

end GlobalTheory.SgInf.BesselExt


open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.bessel_ext_bounded : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hw0 : w ≠ 0 := by
    intro h; have h1 := hStd.2.2.2.1; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hDD := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ
  have hst : ∀ g ∈ GG k r, ∀ u ∈ DD σ w, σ g u ∈ DD σ w := hDD.1
  have hdense : Dense (DD σ w : Set H) := hDD.2.1 hStd.2.2.1 hw0
  have hconc : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by
    rw [ae_iff]; exact hHaar.2.2.1
  let F : H → Mt k r → Wp := fun u x => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)
  let K : ℕ → Set (Mt k r) := fun n => Metric.closedBall 0 n
  have hKm : ∀ n, MeasurableSet (K n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall 0 n
  have hcov : ⋃ n, K n = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈‖x‖⌉₊, ?_⟩
    simp only [K, Metric.mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
  have hsub : ∀ L : Set (Mt k r), IsCompact L → ∃ n, L ⊆ K n := by
    intro L hL
    obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, hR.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil R))⟩
  have hadd : ∀ u ∈ DD σ w, ∀ u' ∈ DD σ w, F (u + u') =ᵐ[μG] fun x => F u x + F u' x := by
    intro u hu u' hu'
    filter_upwards [hconc] with x hx
    exact afun_add hStd hSide hv ξ hu hu' hx
  have hsmul : ∀ (b : ℂ), ∀ u ∈ DD σ w, F (b • u) =ᵐ[μG] fun x => b • F u x :=
    fun b u _ => Filter.Eventually.of_forall fun x => afun_smul b u v ξ _
  obtain ⟨T0, hT0D, hT0add, hT0smul, hT0b⟩ := GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense μG K hKm hcov (DD σ w) hdense F hadd hsmul
    (fun n => GlobalTheory.T.lintegral_besselCoefficient_compact_le k r σ w a μG d z c π μS hStd hSide v hv ξ (K n) (hKc n))
  have hT0m : ∀ u, AEStronglyMeasurable (T0 u) μG := by
    intro u
    have h : AEStronglyMeasurable (T0 u) (μG.restrict (⋃ n, K n)) :=
      aestronglyMeasurable_iUnion_iff.2 fun n => ((hT0b n).choose_spec u).1
    rwa [hcov, Measure.restrict_univ] at h
  have hT0bK : ∀ L : Set (Mt k r), IsCompact L → ∃ C : ℝ, ∀ u,
      ∫⁻ x in L, (‖T0 u x‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
    intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => (lintegral_mono_set hn).trans (hC u).2⟩
  have hT0sub : ∀ u u', (fun x => T0 u x - T0 u' x) =ᵐ[μG] T0 (u - u') := by
    intro u u'
    filter_upwards [hT0add (u - u') u'] with x hx
    rw [sub_add_cancel] at hx
    rw [hx]; simp
  have hmeasn : ∀ u, AEMeasurable (fun x => (‖T0 u x‖₊ : ENNReal) ^ 2) μG := fun u =>
    (hT0m u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2
  refine ⟨fun u M => T0 u (Matrix.of.symm M), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; funext M; show T0 u _ = _; rw [hT0D u hu]; rfl
  · intro u u'; exact hT0add u u'
  · intro b u; exact hT0smul b u
  · intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => ⟨(hC u).1.mono_measure (Measure.restrict_mono hn le_rfl),
      (lintegral_mono_set hn).trans (hC u).2⟩⟩
  · intro y hy u
    have hmp : MeasurePreserving (rmulM y) μG μG :=
      ⟨(continuous_rmulM y).measurable, (GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar).1 y hy⟩
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 (σ y u) x) (fun u x => T0 u (rmulM y x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'
      filter_upwards [hT0sub (σ y u) (σ y u')] with x hx
      rw [hx, map_sub]
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(hC (σ y u)).1, ?_⟩⟩
      rw [← hσ.2.1 y hy u]; exact (hC (σ y u)).2
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_rmulM y))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_rmulM y) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro u hu
      show (fun x => T0 (σ y u) x) =ᵐ[μG] fun x => T0 u (rmulM y x)
      rw [hT0D _ (hst y hy u hu), hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_right hσ u v ξ hx hy
  · intro s hs u
    have hmp : MeasurePreserving (lmulM s : Mt k r → Mt k r) μG μG :=
      ⟨(continuous_lmulM' s).measurable, hHaar.2.2.2 s (hSG hs)⟩
    have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
    have hPin : ‖PiS (psiGen k r z c) π s‖ ≤ 1 := (hPi.2.2.1 s hs).1
    have hnorm : ∀ e : Wp, ‖PiS (psiGen k r z c) π s e‖₊ ≤ ‖e‖₊ := fun e => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact ((PiS (psiGen k r z c) π s).le_opNorm e).trans
        (mul_le_of_le_one_left (norm_nonneg _) hPin)
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 u (lmulM s x)) (fun u x => PiS (psiGen k r z c) π s (T0 u x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro u u'
      filter_upwards [hT0sub u u'] with x hx
      rw [← map_sub, hx]
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_lmulM' s))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_lmulM' s) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(PiS (psiGen k r z c) π s).continuous.comp_aestronglyMeasurable (hC u).1, ?_⟩⟩
      refine le_trans (lintegral_mono fun x => ?_) (hC u).2
      exact pow_le_pow_left₀ (by positivity) (ENNReal.coe_le_coe.2 (hnorm _)) 2
    · intro u hu
      show (fun x => T0 u (lmulM s x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T0 u x)
      rw [hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_left hStd hSide hv ξ hu hs hx hSG
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMatrixCoeffExtendsBoundedEquivariantStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  first | exact @GlobalTheory.SgInf.bessel_ext_bounded | exact GlobalTheory.SgInf.bessel_ext_bounded | (intros; apply GlobalTheory.SgInf.bessel_ext_bounded <;> assumption)
end
end
