module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
public import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAdd

section

@[expose] public section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp [JF.integrand, B.rho, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocPhi

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalSquareIntegrableTransfer

section

@[expose] public section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem local_square_integrable_transfer : LocalSquareIntegrableTransfer := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A ε J e hFr hBg hε hA hJ π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  obtain ⟨F, -, hCC, hFJ⟩ := hJ.2 ε hε
  set A' := A - 5 * Bg with hA'
  have hC5 : ∀ m, m ≤ 5 → B.InCC A' m F := by
    intro m hm
    refine inCC_antiA ?_ (hCC m)
    have : (m : ℝ) ≤ 5 := by exact_mod_cast hm
    rw [hA']; nlinarith

  have hAB : B.AB S.G.k S.G.r ≤ A' := by
    have := jd_AB_le S.G.k S.G.r
    rw [hA']; linarith
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A' hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hC5 4 (by norm_num)
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hC5 5 le_rfl) (hC5 5 le_rfl) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ.1 π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  have hGm : Measurable (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT => MA.Gq (D.parOf S v) q) := by
    unfold MA.Gq; fun_prop
  have hs : MeasurableSet {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q} :=
    measurableSet_le measurable_const hGm
  refine ⟨(((jd_evQ_meas _ _).norm).pow 2).restrict, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q ∈ {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q},
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2) ≤ H q.1 := by
    intro q hqs
    refine ENNReal.ofReal_le_ofReal ?_
    have hGg : ε ≤ GfP S T v (B.gq (T v).base q.1) := by
      have h1 := Formalism.FourierDecayAlt.P.CutMP.cutTr_Gf_gq (T v).base q.2.1 (by rw [hTT]; exact q.2.2)
      have h2 : GfP S T v (B.gq (T v).base q.1) = MA.Gq (D.parOf S v) q := by
        unfold GfP MA.Gq; rw [h1, hTT]
      rw [h2]; exact hqs
    have hJF : J (B.gq Db q.1) = B.JF Db F (B.gq Db q.1) := hFJ q.1 q.2 hGg
    have hq : MA.evQ (D.parOf S v) (trJ S T v e J π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := by
      rw [← hJF]; exact congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          ∂(MA.mu0 (D.parOf S v).r (D.parOf S v).TT).restrict
            {q | ε ≤ MA.Gq (D.parOf S v) q}
        ≤ ∫⁻ q in {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q}, H q.1
            ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT := setLIntegral_mono' hs p1
      _ ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jALocCC_of_op (h2 : JALocOp) (h3 : JALocAdj) : JALocCC :=
  jALocCC_of_leaves h2 h3 local_phi_transfer_holds local_additivity_transfer local_square_integrable_transfer

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
end
