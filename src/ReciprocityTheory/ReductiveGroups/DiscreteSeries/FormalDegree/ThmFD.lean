module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConst
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdPointwise
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdStep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpper
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLower

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by

  have hsq : ∀ y : PCoord ε → ℂ,
      ‖(((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2))) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
    intro y
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 1
    ring
  have htend : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    intro y
    rw [← hsq y]
    exact ENNReal.tendsto_ofReal (((hlim y).norm).pow 2)
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) := by
    intro t
    exact ENNReal.measurable_ofReal.comp
      ((((fdl_inner_continuous (lamT lam t) (T t) (T t).w (T t).w).comp
        (continuous_const_smul _)).norm.pow 2).measurable)
  have key : ∀ t : ℕ, 1 ≤ t →
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
        (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2) ≤
      ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
    have hs : (0 : ℝ) < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
    have hpow : ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = ((t : ℝ) ^ (pOf ε * qOf ε))⁻¹ := by
      rw [pow_mul, inv_pow, Real.sq_sqrt ht0.le, inv_pow]
    conv_rhs => rw [lintegral_pcoord_smul _ hs]
    try rw [show 2 * pOf ε * qOf ε = 2 * (pOf ε * qOf ε) from mul_assoc _ _ _]
    rw [hpow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_mul]
    refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)
  calc ENNReal.ofReal (PiW ε 0)
      = ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := (fdl_gauss ε).symm
    _ = ∫⁻ y : PCoord ε → ℂ, Filter.liminf (fun t : ℕ => ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := by
        congr 1
        funext y
        rw [(htend y).liminf_eq]
    _ ≤ Filter.liminf (fun t : ℕ => ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ _ := by
        refine Filter.liminf_le_liminf ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with t ht using key t ht

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ThmFD

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem thmFD (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hp : 1 ≤ pOf ε)
    (hq : 1 ≤ qOf ε) (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h)
    (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    (H : ℕ → Type) [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (hd : ∀ᶠ t in Filter.atTop, Formalism.MainNotions.S.IsFdeg (muCD ε) (σ t) (dfun (lamT lam t))) :
    dfun lam = dimVlam lam := by
  have hlam0 : lamT lam 0 = lam := by simp [lamT]
  have hanti : Antitone lam := hlam.1.antitone
  have hcP : 0 < cPQ ε := lt_of_lt_of_le (inv_pos.mpr (pow_pos Real.pi_pos _)) (inv_pi_pow_le_cPQ ε)
  have hpos : ∀ t, (0:ℝ) < Module.finrank ℂ (T t).V := fun t => by
    have : Nontrivial (T t).V := ⟨⟨(T t).w, 0, fun h => by
      have h2 := (T t).w_norm
      rw [h, norm_zero] at h2
      exact zero_ne_one h2⟩⟩
    exact_mod_cast Module.finrank_pos
  have h1 : ∀ t, dfun (lamT lam t) / Vand (lamT lam t) = dfun (lamT lam 0) / Vand lam := fun t => by
    rw [hlam0]; exact fd_step dfun hstep hlam hgap t
  have hd0 : 0 < dfun (lamT lam 0) := by
    obtain ⟨t, ht⟩ := hd.exists
    have hv1 : 0 < Vand (lamT lam t) := vand_pos (isHCParam_lamT hlam t).1
    have hv0 : 0 < Vand lam := vand_pos hlam.1
    have e : dfun (lamT lam 0) = Vand lam * (dfun (lamT lam t) / Vand (lamT lam t)) := by
      rw [h1 t]; field_simp
    rw [e]
    have := ht.1
    positivity
  have hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0) := by
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
        (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) ≤ ENNReal.ofReal (cPQ ε) *
        (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
          ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have L6 := lemma6c hFt hdt
      have hdt0 := hdt.1
      have hD := hpos t
      have hA : 0 ≤ (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) := by positivity
      calc ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))
          = ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              ENNReal.ofReal (1 / dfun (lamT lam t)) := by
            rw [← ENNReal.ofReal_mul hA]; congr 1; ring
        _ ≤ ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              (ENNReal.ofReal (cPQ ε / Module.finrank ℂ (T t).V) *
                ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
            gcongr
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
            have e2 : (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) *
                (cPQ ε / Module.finrank ℂ (T t).V) = cPQ ε * (t:ℝ) ^ (pOf ε * qOf ε) := by
              field_simp
            rw [e2, ENNReal.ofReal_mul hcP.le, mul_assoc]
    refine le_trans (Filter.limsup_le_limsup hev) ?_
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
    exact formal_degree_limsup_upper_bound hanti
  have hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop := by
    have hL := formal_degree_liminf_lower_bound T (matrix_coefficient_pointwise_limit hB3 H σ T j hF hsm)
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) ≤
        ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have F3 := lintegral_fF_coeff_sq_le_finrank_div_fdeg hFt hdt
      calc _ = ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) * (ENNReal.ofReal (cPQ ε) *
            ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) := by
            ring
        _ ≤ ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
              ENNReal.ofReal ((Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_div_assoc]
    refine le_trans ?_ (Filter.liminf_le_liminf hev)
    rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
  have := formal_degree_constant_eq hlam (fun t => dfun (lamT lam t)) T h1 hd0 hup hlow
  simpa only [hlam0] using this

end ReciprocityTheory.ChartRestriction.DS
end
end
end
