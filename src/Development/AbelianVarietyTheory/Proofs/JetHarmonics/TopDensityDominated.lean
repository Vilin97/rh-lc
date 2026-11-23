module

public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficientsStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompExpIteratedDerivBounded

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology

theorem cutoff_comp_exp_iteratedDeriv_bounded (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv p (fun t => χ (Real.exp t)) t| ≤ C := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hc : ∀ k t : ℝ, iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
    intro k t
    cases p with
    | zero => simp
    | succ n => simp [iteratedDeriv_succ']
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hs.comp Real.contDiff_exp
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log δ → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have := Real.exp_lt_exp.mpr hs
      rw [Real.exp_log hδ] at this
      simp only [hh, h0 _ this]
    rw [this.iteratedDeriv_eq p, hc]; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, h1 _ this]
    rw [this.iteratedDeriv_eq p, hc]
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log δ) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases lt_or_ge t (Real.log δ) with h1 | h1
  · rw [hlow t h1]; simp
  · rcases lt_or_ge 0 t with h2 | h2
    · rw [hhigh t h2]; split_ifs <;> simp
    · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)

theorem ld_cut_pow_bound (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (e j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  choose B hB0 hB using cutoff_comp_exp_iteratedDeriv_bounded χ hχ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (e : ℝ) ^ (j - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i)) (by positivity), ?_⟩
  intro ε x hε hx
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχ.1.comp Real.contDiff_exp
  unfold LE.ld
  have e1 : (fun u : ℝ => χ (Real.exp u / ε) * Real.exp u ^ e) =
      fun u : ℝ => h (u - Real.log ε) * Real.exp ((e : ℝ) * u) := by
    funext u
    simp only [hh]
    rw [Real.exp_sub, Real.exp_log hε, Real.exp_nat_mul]
  have c1 : ContDiff ℝ j (fun u : ℝ => h (u - Real.log ε)) :=
    (hsm.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have c2 : ContDiff ℝ j (fun u : ℝ => Real.exp ((e : ℝ) * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  beta_reduce
  rw [e1, iteratedDeriv_fun_mul c1.contDiffAt c2.contDiffAt, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedDeriv_comp_sub_const, iteratedDeriv_exp_const_mul]
  beta_reduce
  rw [Real.exp_nat_mul, Real.exp_log hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j.choose i : ℝ)),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (e : ℝ) ^ (j - i) * x ^ e), ← mul_assoc]
  have := hB i (Real.log x - Real.log ε)
  gcongr

theorem ld_cut_pow : ∀ (χ : ℝ → ℝ) (e J : ℕ), C6.IsCut0 χ →
    (∀ ε : ℝ, 0 < ε → CutPow e fun y => χ (y / ε) * y ^ e) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → ∀ j, j ≤ J →
        |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  intro χ e J hχ
  constructor
  · intro ε hε
    obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
    refine ⟨(hs.comp (contDiff_id.div_const ε)).mul (contDiff_id.pow e), ⟨δ * ε, by positivity, fun x hx => ?_⟩,
      1, ε, fun x hx => ?_⟩
    · have : x / ε < δ := by rwa [div_lt_iff₀ hε]
      simp [h0 _ this]
    · have : 1 ≤ x / ε := by rwa [le_div_iff₀ hε, one_mul]
      simp [h1 _ this]
  · choose C hC0 hC using ld_cut_pow_bound χ hχ e
    refine ⟨∑ j ∈ Finset.range (J + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun ε x hε hx j hj => ?_⟩
    refine (hC j ε x hε hx).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NeZeroOfIsLocPt

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.TopDensityBound

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_comp_sq_le (E : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (E.comp X)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact E.le_opNorm _

variable {P : M.Par}

theorem V_eq_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (h : ¬ 0 < TBB.Gp p γ) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dite_eq_right]
  exact fun h' => h h'.2

theorem RR_cons (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (hw : w ≠ [])
    {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR F (P.r + 1) w γ γ = ((∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
      Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e F) γ))‖ ^ 2 : ℝ) : ℂ) := by
  have : p.RR F (P.r + 1) w γ γ = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w γ γ := by
    simp [KB.Pl.RR, D.RRplace, hγ, hw]
  rw [this]
  unfold Top.topOf
  push_cast
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  simp only [TBB.TTp, KB.Pl.V]
  push_cast
  ring

theorem Ew_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) w γ =
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)) *
        (p.RR F (P.r + 1) w γ γ).re := by
  unfold TBB.Ew TBB.NP TBB.normC
  rw [Complex.re_ofReal_mul]
  simp

theorem ne_zero_of_isLocPt {r : ℕ} (c : Fin (r + 1) → ℂ) (h : D.IsLocPt (TBB.bigPt r c) (r + 1)) (l : Fin (r + 1)) :
    c l ≠ 0 := by
  have := h.1 (1, c l) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨l, rfl⟩)
  exact this.2

theorem wPt_bigPt (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) = ‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c) := by
  unfold Top.wPt TBB.Gp
  have h : D.ptMatN (TBB.bigPt P.r c) (P.r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Complex.normSq_eq_norm_sq]

end aux

theorem top_density_le : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬((∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = 0) ∧ ((∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) ∧ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) = TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 ∧ |TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)| ≤ C * TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * (‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length * ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) := by
  intro Wp Wq _ _ _ _ _ _ P p w
  set K : Ix (Fin w.length) → ℝ := fun e => ∑ ρ : M.Ty P, |(Top.cW P p.l0 w e ρ).re| * ‖p.TP.E ρ‖ ^ 2 with hK
  have hK0 : ∀ e, 0 ≤ K e := fun e => Finset.sum_nonneg fun ρ _ => by positivity
  have hS0 : 0 ≤ ∑ e, K e := Finset.sum_nonneg fun e _ => hK0 e
  refine ⟨1 + ∑ e, K e, by linarith, fun H c => ⟨fun hn => ?_, fun hc hG => ?_⟩⟩
  · rw [Ew_eq]
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := fun h => hn ⟨ne_zero_of_isLocPt c hl, h⟩
      by_cases hw : w = []
      · subst hw
        rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top p H hl, V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self,
          Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
        simp
      · rw [RR_cons p H w hw hl]
        simp [V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
    · have : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) = 0 := by
        simp [KB.Pl.RR, D.RRplace, hl]
      rw [this]; simp
  · have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
    have hn : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) := by
      unfold TBB.TTp
      rw [Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt _ _ _ _ c hζ.le]
      exact Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _
    have hnil : TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) =
        TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
      rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hl, Real.mul_self_sqrt hn]
    refine ⟨hn, hnil, ?_⟩
    by_cases hw : w = []
    · subst hw
      rw [hnil, abs_of_nonneg (by positivity)]
      simp only [p.Θ.nil, List.length_nil, pow_zero, mul_one]
      rw [Finset.sum_const]
      have hcard : (Finset.univ : Finset (Ix (Fin 0))).card = 1 := by simp [Ix]
      rw [hcard, one_smul]
      have : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
        positivity
      rw [mul_assoc]
      exact le_mul_of_one_le_left this (le_add_of_nonneg_right hS0)
    · rw [Ew_eq, Real.mul_self_sqrt hn, RR_cons p H w hw hl, Complex.ofReal_re, abs_of_nonneg (by positivity),
        ← wPt_bigPt]
      set Wt := Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) with hWt
      have hW0 : 0 ≤ Wt := by rw [hWt, wPt_bigPt]; positivity
      have key : (∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
          Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
            ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2) ≤
          (1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        set v := ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 with hv
        have hv0 : 0 ≤ v := by positivity
        have hKe : K e ≤ 1 + ∑ e, K e := by
          have := Finset.single_le_sum (f := K) (fun e _ => hK0 e) (Finset.mem_univ e)
          linarith
        calc _ ≤ K e * Wt ^ w.length * v := by
              simp only [hK]
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_le_sum fun ρ _ => ?_
              have h1 : Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 ≤
                  Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re| := by
                unfold Top.dH
                rw [← hWt, Real.sq_sqrt']
                exact max_le (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
              have h2 := hsVec_comp_sq_le (p.TP.E ρ) (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))
              calc _ ≤ (Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re|) * (‖p.TP.E ρ‖ ^ 2 * v) :=
                    mul_le_mul h1 h2 (by positivity) (by positivity)
                _ = _ := by ring
          _ ≤ _ := by gcongr
      calc _ ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ((1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left key hn
        _ = _ := by ring

end GlobalTheory.TopDensityBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem dom_pow_le (G : ℝ) (hG : 0 < G) (m q : ℕ) (h : m ≤ q) : G ^ m ≤ 1 + G ^ q := by
  rcases le_total G 1 with h1 | h1
  · have := pow_le_one₀ (n := m) hG.le h1
    have := pow_pos hG q
    linarith
  · have := pow_le_pow_right₀ h1 h
    linarith

theorem dom_real_bound {ι κ : Type} [Fintype ι] [Fintype κ] (E Ct n D G C S C' : ℝ) (L a p₀ : ℕ)
    (u : ι → ℝ) (v : κ → ℝ) (hCt : 0 ≤ Ct) (hn : 0 ≤ n) (hD : 0 < D) (hG : 0 < G) (hC : 0 ≤ C)
    (hS0 : 0 ≤ S) (hS : S ≤ C' * G ^ p₀) (hu0 : ∀ e, 0 ≤ u e) (hv0 : ∀ t, 0 ≤ v t)
    (hL : L * (1 + 2 * a) ≤ 2 * p₀)
    (hu : ∀ e, u e ≤ C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * S * ∑ t, v t)
    (hE : E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2) :
    E ≤ (Ct * Fintype.card ι * (C * C') ^ 2 * Fintype.card κ) *
      ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hL
  have hT0 : 0 ≤ ∑ t, v t := Finset.sum_nonneg fun t _ => hv0 t
  have hT : (∑ t, v t) ^ 2 ≤ Fintype.card κ * ∑ t, v t ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := v)
  have hV0 : 0 ≤ ∑ t, v t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : ∑ e, u e ^ 2 ≤ Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
    have : ∀ e ∈ (Finset.univ : Finset ι),
        u e ^ 2 ≤ (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
      intro e _
      refine pow_le_pow_left₀ (hu0 e) ((hu e).trans ?_) 2
      gcongr
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have h2 : (D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2 = G ^ m := by
    have e : (G ^ p₀) ^ 2 = G ^ L * (G ^ (a * L)) ^ 2 * G ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [mul_comm p₀ 2, hm]; ring
    rw [mul_pow, e, div_pow, inv_pow, inv_pow, ← pow_mul D 2 L, mul_comm 2 L, pow_mul D L 2]
    have := pow_pos hD L
    have := pow_pos hG L
    have := pow_pos hG (a * L)
    field_simp
  have h3 : G ^ m ≤ 1 + (G ^ p₀) ^ 2 := by
    rw [← pow_mul]
    exact dom_pow_le G hG _ _ (by omega)
  have h4 : ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) = n * (1 + (G ^ p₀) ^ 2) * ∑ t, v t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2 := hE
    _ ≤ Ct * n * (D ^ 2 / G) ^ L *
        (Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2) := by gcongr
    _ = Ct * n * Fintype.card ι * (C * C') ^ 2 *
        ((D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2) * (∑ t, v t) ^ 2 := by ring
    _ ≤ Ct * n * Fintype.card ι * (C * C') ^ 2 * (1 + (G ^ p₀) ^ 2) * (Fintype.card κ * ∑ t, v t ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by rw [h4]; ring

theorem dom_thr (Cc r k : ℝ) (N L : ℝ) (hCc : 8 ≤ Cc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hL : L ≤ N) (hN : 0 ≤ N) :
    L * (8 * (r + 1) * (2 * r + k + 1)) ≤ Cc * (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2) := by
  have h1 : r + 1 ≤ (r + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : 2 * r + k + 1 ≤ (2 * r + k + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc L * (8 * (r + 1) * (2 * r + k + 1)) ≤ N * (Cc * (r + 1) ^ 4 * (2 * r + k + 1) ^ 2) := by
        have : 0 ≤ Cc := by linarith
        gcongr
    _ = _ := by ring

theorem top_density_dominated : GlobalTheory.HCXi.BesselXiIntegrable → ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) (w : List C.Letter), C6.IsCut0 χ → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) → N * (1 + 2 * a P.r) ≤ 2 * p₀ → KB.CutWord P p.l0 w → w.length ≤ N → (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ ε : ℝ, 0 < ε → ∀ c₀ : Fin (P.r + 1) → ℂ, ‖(fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) c₀‖ ≤ h c₀ := by
  intro hXi a ha Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.wordBound_smooth_decaying_coefficients a ha Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients hXi
  refine ⟨max C1 (max C2 8), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N w hχ hDD hf hfA hth hN hw hwN
  have hc1 : C1 ≤ max C1 (max C2 8) := le_max_left _ _
  have hc2 : C2 ≤ max C1 (max C2 8) := (le_max_left _ _).trans (le_max_right _ _)
  have hc8 : 8 ≤ max C1 (max C2 8) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max C1 (max C2 8) = Cc at hth hc1 hc2 hc8
  obtain ⟨C, J, Θs, hC, hpoly, hb⟩ := h1 Wp Wq P p N w hDD hw hwN
  obtain ⟨hcut, C', hC', hld⟩ := ld_cut_pow χ p₀ J hχ
  obtain ⟨Ct, hCt, htop⟩ := GlobalTheory.TopDensityBound.top_density_le Wp Wq P p w
  constructor
  · intro ε hε
    have hs := (GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P p.T.base p₀ 0 _ f A₀ (hcut ε hε) hf (hfA 0)).1
    have hm := GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb _ w hDD hw hs
    simp only [GlobalTheory.TopVec.Ew_eq_norm_tv_sq]
    exact hm.norm.pow 2
  have hth1 : C1 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (2 * (P.r : ℝ) + 2) * p₀ := by
    refine le_trans ?_ (hth.trans (le_of_eq (by push_cast; ring)))
    gcongr
  set d : ℝ := ((w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) with hd
  have hth2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    have e1 := dom_thr Cc P.r P.k N w.length hc8 (by positivity) (by positivity) (by exact_mod_cast hwN) (by positivity)
    have e2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤
        Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by gcongr
    have e3 : d = (w.length : ℝ) * (8 * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1)) := by
      rw [hd]; push_cast; ring
    rw [mul_add] at hth
    linarith
  have hΘ : ∀ t : Fin Θs.length, B.CkOn ⊤ (B.GV P.k P.r) (B.opApply Θs[t.1] f) ∧
      ∀ m : ℕ, B.InCC (A₀ - d) m (B.opApply Θs[t.1] f) := fun t =>
    Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq _ d A₀ (by positivity)
      ((polyOp_ok P.k P.r Wp Wq _ _ _ (hpoly _ (List.getElem_mem t.2))).2.1 d le_rfl) f hf hfA
  refine ⟨fun c => (Ct * Fintype.card (Ix (Fin w.length)) * (C * ((J + 1) * C')) ^ 2 * Fintype.card (Fin Θs.length)) *
    ∑ t : Fin Θs.length, (TBB.Ew p (fun _ => 1) (B.opApply Θs[t.1] f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Θs[t.1] f g)
        (P.r + 1) [] (TBB.bigPt P.r c)), ?_, ?_⟩
  · refine Integrable.const_mul (integrable_finsetSum _ fun t _ => Integrable.add ?_ ?_) _
    · refine h2 Wp Wq P p _ (A₀ - d) (hΘ t).1 (hΘ t).2 (hth2.trans ?_)
      have : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by positivity
      linarith
    · exact h2 Wp Wq P p _ _ (Formalism.FourierDecayAlt.P.CutBP.ckOn_Gpow_smul _ _ p₀ (hΘ t).1)
        (Formalism.FourierDecayAlt.P.CutBP.inCC_Gpow_smul _ _ p₀ (hΘ t).2) hth2
  intro ε hε c
  beta_reduce
  by_cases hc : (∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [(htop _ c).1 hc, norm_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      add_nonneg (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _))
  obtain ⟨hc0, hG⟩ := hc
  obtain ⟨hn, -, hE⟩ := (htop (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) c).2 hc0 hG
  have hGp : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) (TBB.bigPt P.r c) =
        ((TBB.Gp p (TBB.bigPt P.r c) ^ p₀ : ℝ) : ℂ) • p.V F (TBB.bigPt P.r c) := by
    intro F
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · exact Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p F p₀ hl hG
    · rw [Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), smul_zero]
  simp only [fun H => ((htop H c).2 hc0 hG).2.1, hGp, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  rw [Real.norm_eq_abs]
  refine dom_real_bound _ Ct _ ‖∏ l, c l‖ _ C
    (∑ j ∈ Finset.range (J + 1), |LE.ld j (fun y => χ (y / ε) * y ^ p₀) (TBB.Gp p (TBB.bigPt P.r c))|) _
    w.length (a P.r) p₀ _ (fun t : Fin Θs.length => ‖B.hsVec (p.V (B.opApply Θs[t.1] f) (TBB.bigPt P.r c))‖)
    hCt hn (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => hc0 l)) hG hC
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((Nat.mul_le_mul_right _ hwN).trans hN) ?_ hE
  · have := Finset.sum_le_card_nsmul (Finset.range (J + 1)) _ _ fun j hj =>
      hld ε _ hε hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    simpa [mul_assoc] using this
  · intro e
    have := hb _ f ⟨p₀, A₀, hcut ε hε, hf, hfA, hth1⟩ e c hc0 hG
    rwa [← Fin.sum_univ_fun_getElem] at this

end GlobalTheory.HatNF
end
end
