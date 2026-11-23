module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivationOfQuadraticForm
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LieCPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top4
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.NormIterFstComp

section

@[expose] public section

noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

section general

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iter_snd (q : ℝ × E) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun q : ℝ × E => q.2) q‖ ≤ 1 + ‖q.2‖ := by
  have e : (fun q : ℝ × E => q.2) = ⇑(ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rcases l with _ | l
  · rw [norm_iteratedFDeriv_zero]; linarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have hf : fderiv ℝ (fun q : ℝ × E => q.2) = fun _ => ContinuousLinearMap.snd ℝ ℝ E := by
      funext y; rw [e]; exact (ContinuousLinearMap.snd ℝ ℝ E).fderiv
    rw [hf]
    rcases l with _ | l
    · rw [norm_iteratedFDeriv_zero]
      linarith [ContinuousLinearMap.norm_snd_le ℝ ℝ E, norm_nonneg q.2]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iter_fst_comp {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ ∞ A) (q : ℝ × E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ ≤ ‖iteratedFDeriv ℝ j A q.1‖ := by
  have e : (fun q : ℝ × E => A q.1) = A ∘ ⇑(ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hA _ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ E

theorem bound_comp (φ : SchwartzMap E ℂ) (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (hinv : ∀ t y, A (-t) (A t y) = y) (k N : ℕ) :
    ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (fun q : ℝ × E => φ (A q.1 q.2)) (p, x)‖ ≤ C := by
  obtain ⟨KA, hKA⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun s => ∑ j ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ j A s‖)
    (continuous_finsetSum _ (fun j _ => (hA.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm)).continuousOn
  have hj : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ j ≤ N, ‖iteratedFDeriv ℝ j A s‖ ≤ KA := by
    intro s hs j hjN
    have h1 := hKA s hs
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j A s‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hjN))).trans h1
  have hKA0 : 0 ≤ KA := (norm_nonneg _).trans (hj 0 (by norm_num) 0 (Nat.zero_le _))
  have hAn : ∀ s ∈ Icc (-1 : ℝ) 1, ‖A s‖ ≤ KA := fun s hs => by
    have := hj s hs 0 (Nat.zero_le _); rwa [norm_iteratedFDeriv_zero] at this
  set f : ℝ × E → E := fun q => A q.1 q.2 with hfdef
  have hf : ContDiff ℝ ∞ f := (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hDf : ∀ q : ℝ × E, q.1 ∈ Icc (-1 : ℝ) 1 → ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i f q‖ ≤ 2 ^ i * KA * (1 + ‖q.2‖) := by
    intro q hq i hi
    have hb := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).norm_iteratedFDeriv_le_of_bilinear
      (f := fun q : ℝ × E => A q.1) (g := fun q : ℝ × E => q.2) (hA.comp contDiff_fst) contDiff_snd q
      (n := i) (by exact_mod_cast le_top)
    have e : (fun y : ℝ × E => (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) (A y.1) y.2) = f := rfl
    rw [e] at hb
    refine hb.trans ?_
    have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖ ≤ (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) := by
      intro j hjm
      have hjN : j ≤ N := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hjm)).trans hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul ((norm_iter_fst_comp hA q j).trans (hj q.1 hq j hjN))
        (norm_iter_snd q _) (norm_nonneg _) hKA0) (by positivity)
    calc ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ * ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖
        ≤ 1 * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) :=
          mul_le_mul ContinuousLinearMap.norm_id_le (Finset.sum_le_sum hterm)
            (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
      _ = 2 ^ i * KA * (1 + ‖q.2‖) := by
          rw [one_mul, ← Finset.sum_mul]
          have := Nat.sum_range_choose i
          have h2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by exact_mod_cast this
          rw [h2]; ring
  set S := 2 ^ (k + N) * ((Finset.Iic (k + N, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ with hSdef
  have hS : ∀ y, ∀ i ≤ N, (1 + ‖y‖) ^ (k + N) * ‖iteratedFDeriv ℝ i φ y‖ ≤ S := fun y i hi =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, N)) le_rfl hi φ y
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0 0 (Nat.zero_le _))
  set KD := max 1 (2 ^ N * KA) with hKD
  set K' := max 1 KA with hK'
  have hKD1 : 1 ≤ KD := le_max_left _ _
  have hK'1 : 1 ≤ K' := le_max_left _ _
  refine ⟨N.factorial * S * KD ^ N * K' ^ (k + N), fun p hp x => ?_⟩
  have hp' : p ∈ Icc (-1 : ℝ) 1 := by
    rw [sub_zero, Real.norm_eq_abs] at hp; exact ⟨by linarith [neg_abs_le p], (le_abs_self p).trans hp⟩
  have hmp : -p ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp'.2], by linarith [hp'.1]⟩
  set y := f (p, x) with hy
  have hxy : ‖x‖ ≤ KA * ‖y‖ := by
    have e1 : x = A (-p) y := (hinv p x).symm
    calc ‖x‖ = ‖A (-p) y‖ := by rw [← e1]
      _ ≤ ‖A (-p)‖ * ‖y‖ := (A (-p)).le_opNorm y
      _ ≤ KA * ‖y‖ := by gcongr; exact hAn _ hmp
  have h1x : 1 + ‖x‖ ≤ K' * (1 + ‖y‖) := by
    have h2 : KA * ‖y‖ ≤ K' * ‖y‖ := by gcongr; exact le_max_right _ _
    nlinarith [norm_nonneg y]
  have hyp : 0 < (1 + ‖y‖) ^ (k + N) := by positivity
  have hC : ∀ i ≤ N, ‖iteratedFDeriv ℝ i φ (f (p, x))‖ ≤ S / (1 + ‖y‖) ^ (k + N) := by
    intro i hi
    rw [le_div_iff₀ hyp, mul_comm]
    exact hS y i hi
  have hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f (p, x)‖ ≤ (KD * (1 + ‖x‖)) ^ i := by
    intro i hi1 hiN
    have hb1 : 1 ≤ KD * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    refine (hDf (p, x) hp' i hiN).trans ?_
    have h3 : 2 ^ i * KA ≤ KD := by
      refine le_trans ?_ (le_max_right _ _)
      gcongr
      · norm_num
    calc 2 ^ i * KA * (1 + ‖(p, x).2‖) ≤ KD * (1 + ‖x‖) := by gcongr
      _ ≤ (KD * (1 + ‖x‖)) ^ i := le_self_pow₀ hb1 (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le (g := ⇑φ) (f := f) (φ.smooth ⊤) hf (n := N)
    (by exact_mod_cast le_top) (p, x) hC hD
  have e2 : (fun q : ℝ × E => φ (A q.1 q.2)) = ⇑φ ∘ f := rfl
  rw [e2]
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  have hpow : (1 + ‖x‖) ^ (k + N) ≤ K' ^ (k + N) * (1 + ‖y‖) ^ (k + N) := by
    rw [← mul_pow]; gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (⇑φ ∘ f) (p, x)‖
      ≤ (1 + ‖x‖) ^ k * (N.factorial * (S / (1 + ‖y‖) ^ (k + N)) * (KD * (1 + ‖x‖)) ^ N) := by
        gcongr
    _ = N.factorial * S * KD ^ N * ((1 + ‖x‖) ^ (k + N) / (1 + ‖y‖) ^ (k + N)) := by
        rw [mul_pow, pow_add]; field_simp; ring
    _ ≤ N.factorial * S * KD ^ N * K' ^ (k + N) := by
        gcongr
        rw [div_le_iff₀ hyp]; exact hpow

end general

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDeriv

section

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob

open SchDH

theorem schDeriv : SchDeriv := by
  intro m n c hc X P
  obtain ⟨φ0, hφ0⟩ := exists_fP (m := m) (n := n) c hc P
  obtain ⟨φ1, hφ1⟩ := exists_fP (m := m) (n := n) c hc (vfX c X P)
  set A : ℝ → (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
    fun t => matL (NormedSpace.exp ((t : ℂ) • X)) with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_A X
  have hinv : ∀ t y, A (-t) (A t y) = y := by
    intro t y
    simp only [hAdef]
    rw [← matL_mul, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    rw [← add_smul, Complex.ofReal_neg, neg_add_cancel, zero_smul, NormedSpace.exp_zero, matL_one]
  let Aeq : ℝ → (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) := fun t =>
    ContinuousLinearEquiv.equivOfInverse (A t) (A (-t)) (fun y => hinv t y)
      (fun y => by have h := hinv (-t) y; rwa [neg_neg] at h)
  have hAeq : ∀ t y, Aeq t y = A t y := fun t y => rfl
  let S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ := fun t => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Aeq t) φ0
  have hS : ∀ t y, S t y = φ0 (A t y) := fun t y => by
    simp only [S, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hAeq]
  refine ⟨S, φ1, fun t y => ?_, fun y => hφ1 y, ?_⟩
  · rw [hS, hφ0]
    congr 1
  · set F : ℝ × (Fin m → Fin n → ℂ) → ℂ := fun q => φ0 (A q.1 q.2) with hFdef
    have hF : ContDiff ℝ ∞ F := (φ0.smooth ⊤).comp ((hA.comp contDiff_fst).clm_apply contDiff_snd)
    have hR : ∀ p, ⇑(S p) = fun x => F (p, x) := fun p => by funext x; rw [hS]
    have hder : ∀ x, HasDerivAt (fun t : ℝ => F (t, x)) (φ1 x) 0 := fun x => by
      have h := hasDerivAt_curve c X P x
      rw [hφ1]
      have e : (fun t : ℝ => F (t, x)) = fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x) := by
        funext t; simp only [hFdef, hAdef, hφ0]
      rw [e]; exact h
    have hD : ∀ v : ℝ, ⇑(v • φ1) = fun x => fderiv ℝ F ((0 : ℝ), x) (v, 0) := by
      intro v
      funext x
      have hFd : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), x)) ((0 : ℝ), x) :=
        ((hF.differentiable (by simp)) _).hasFDerivAt
      have hc : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (Fin m → Fin n → ℂ))) ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
      have h1 := hFd.comp_hasDerivAt (0 : ℝ) hc
      have h2 := (hder x).unique h1
      have e : ((v, 0) : ℝ × (Fin m → Fin n → ℂ)) = v • ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) := by
        ext <;> simp
      rw [SchwartzMap.smul_apply, e, map_smul]
      change v • φ1 x = v • (fderiv ℝ F ((0 : ℝ), x)) ((1 : ℝ), (0 : Fin m → Fin n → ℂ))
      rw [h2]
    have hb : ∀ k N : ℕ, ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : Fin m → Fin n → ℂ,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ N F (p, x)‖ ≤ C := fun k N => bound_comp φ0 A hA hinv k N
    rw [(schwartz_withSeminorms ℂ (Fin m → Fin n → ℂ) ℂ).tendsto_nhds]
    rintro ⟨k, N⟩ ε hε
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.OM.SchDiff.seminorm_remainder hF (0 : ℝ) hb S (fun v => v • φ1) hR hD k N
    set C' := max C 1 with hC'
    have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < min 1 (ε / C') := by
      have h := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [abs_zero] at h
      exact h (Iio_mem_nhds (lt_min one_pos (div_pos hε hC'0)))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have htne' : t ≠ 0 := htne
    have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact (lt_of_lt_of_le ht (min_le_left _ _)).le
    have key : t⁻¹ • (S t - S 0) - φ1 = ((t⁻¹ : ℝ) : ℂ) • (S (0 + t) - S 0 - t • φ1) := by
      rw [Complex.coe_smul, zero_add]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ htne', one_smul]
    change SchwartzMap.seminorm ℂ k N (t⁻¹ • (S t - S 0) - φ1) < ε
    rw [key, map_smul_eq_mul, Complex.norm_real, norm_inv]
    have hCt := hC t ht1
    have hpos : 0 < ‖t‖ := norm_pos_iff.2 htne'
    calc ‖t‖⁻¹ * (SchwartzMap.seminorm ℂ k N) (S (0 + t) - S 0 - t • φ1)
        ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
      _ = C * ‖t‖ := by field_simp
      _ ≤ C' * ‖t‖ := by gcongr; exact le_max_left _ _
      _ < C' * (ε / C') := by
          gcongr
          rw [Real.norm_eq_abs]; exact lt_of_lt_of_le ht (min_le_right _ _)
      _ = ε := by field_simp

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem awayFact_of (hA : AwayAct) (hD : DecompAway) : AwayFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  have hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι := by
    obtain ⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩ := hC
    exact ⟨hθ, hι⟩
  obtain ⟨x, y, hx, hg, -⟩ := hD D n θ τ ι hθι.1 hθι.2 g
  obtain ⟨A, hA'⟩ := hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx
  exact ⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top6

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem top6 (hF : FTfact) (hG : GenA) (hSD : SchDeriv) (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  have hAA : AwayAct := awayAct_of hG hF decompAway
  top5 (locFact_of decomp (opGen_of hF)) hAA
    (lieComm_of awayIn lNe schFP (opCLM_of' hF) (awayFact_of hAA decompAway) hSD) hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top7

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem top7 (hG : GenA) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top6 fTfact hG schDeriv (derivOne wtc) hId hC

end PositivityTheory.Rg.Sw.Glob
end
end
