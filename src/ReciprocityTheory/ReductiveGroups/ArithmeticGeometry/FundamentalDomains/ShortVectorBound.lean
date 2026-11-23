module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBoundOfCoefficientBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorSixthLemmaPrimeHolds

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CountingExponentialSumHolds

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Finset

theorem pow_le_exp_of_log_bound {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have hm0 : 0 < m := by linarith
  have hKm : 0 < K * m := mul_pos hK0 hm0
  have h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : N * (m / (2 * N)) = m / 2 := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hN0.le
  rw [Real.rpow_def_of_pos hKm]
  apply Real.exp_le_exp.mpr
  rw [h1]
  nlinarith

theorem counting_exponential_sum_holds : CountingExponentialSum := by
  intro K N w hK hN hw ι t ht hcount
  classical
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have ht3 : ∀ j, 3 < t j := fun j => by linarith [ht j]
  have hpi := Real.pi_gt_three
  set q : ℝ := Real.exp (2 - Real.pi) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    have h2 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hq12 : q < 1 / 2 := lt_trans hq1 he1
  have hbound : ∀ s : Finset ι, ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤
      Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
    intro s
    obtain ⟨mj, hmj⟩ : ∃ mj : ι → ℕ, mj = fun j => ⌈t j⌉₊ := ⟨_, rfl⟩
    have hmj_ge : ∀ j, t j ≤ (mj j : ℝ) := fun j => by rw [hmj]; exact Nat.le_ceil _
    have hmj_lt : ∀ j, (mj j : ℝ) < t j + 1 := fun j => by
      rw [hmj]; exact Nat.ceil_lt_add_one (by linarith [ht3 j])
    have hmj4 : ∀ j, 4 ≤ mj j := fun j => by
      have h1 : (3 : ℝ) < mj j := lt_of_lt_of_le (ht3 j) (hmj_ge j)
      have h2 : (3 : ℕ) < mj j := by exact_mod_cast h1
      omega
    have step1 : ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
      Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr (by have := hmj_lt j; nlinarith [Real.pi_pos]))
    have step2 : ∀ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y),
        Real.exp (-Real.pi * ((mj j : ℝ) - 1)) ≤ Real.exp (Real.pi - w - 2) * q ^ y := by
      intro y hy
      obtain ⟨j0, _, hj0y⟩ := Finset.mem_image.mp hy
      have hyT : w + N * Real.log (2 * K * N) + N + 2 ≤ (y : ℝ) := by
        rw [← hj0y]; linarith [ht j0, hmj_ge j0]
      have hy1 : (1 : ℝ) ≤ y := by linarith
      have hsum : ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) =
          ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1)) := by
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const,
          nsmul_eq_mul]
      have hcard : ((s.filter (fun j => mj j = y)).card : ℝ) ≤ Real.exp (2 * y - w - 2) := by
        obtain ⟨hfin, hle⟩ := hcount y hy1
        have hsub : ((s.filter (fun j => mj j = y) : Finset ι) : Set ι) ⊆ {j | t j ≤ (y : ℝ)} := by
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          show t j ≤ (y : ℝ)
          rw [← hj'.2]
          exact hmj_ge j
        have h1 : (s.filter (fun j => mj j = y)).card ≤ {j | t j ≤ (y : ℝ)}.ncard := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub hfin
        calc ((s.filter (fun j => mj j = y)).card : ℝ) ≤ ({j | t j ≤ (y : ℝ)}.ncard : ℝ) := by
              exact_mod_cast h1
          _ ≤ (K * y) ^ N := hle
          _ ≤ Real.exp (2 * y - w - 2) := pow_le_exp_of_log_bound hK hN hw hyT
      rw [hsum]
      calc ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1))
          ≤ Real.exp (2 * y - w - 2) * Real.exp (-Real.pi * ((y : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = Real.exp (Real.pi - w - 2) * q ^ y := by
            rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    have step3 : ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y ≤
        Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc ∑ y ∈ s.image mj, q ^ y ≤ ∑ y ∈ Finset.Ico 4 (s.sup mj + 1), q ^ y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro y hy
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
              rw [Finset.mem_Ico]
              exact ⟨hmj4 j, Nat.lt_succ_of_le (Finset.le_sup hj)⟩
            · intro y _ _
              exact pow_nonneg hq0 y
        _ ≤ q ^ 4 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    calc ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) := step1
      _ = ∑ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
          (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem mj hj) _).symm
      _ ≤ ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y := Finset.sum_le_sum step2
      _ ≤ _ := step3
  have hnn : ∀ j, 0 ≤ Real.exp (-Real.pi * t j) := fun j => (Real.exp_pos _).le
  have hsumm : Summable (fun j => Real.exp (-Real.pi * t j)) := summable_of_sum_le hnn hbound
  refine ⟨hsumm, ?_⟩
  have htsum : ∑' j, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) :=
    hsumm.tsum_le_of_sum_le hbound
  have h2w : (2 : ℝ) ^ (w / 2) ≤ Real.exp w := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log 2 < 2 := by linarith [Real.log_two_lt_d9]
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have hq4 : q ^ 4 = Real.exp (8 - 4 * Real.pi) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpos : 0 < 1 - q := by linarith
  calc (2 : ℝ) ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j)
      ≤ Real.exp w * (Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))) :=
        mul_le_mul h2w htsum (tsum_nonneg hnn) (Real.exp_pos _).le
    _ = Real.exp (6 - 3 * Real.pi) / (1 - q) := by
        rw [hq4, show Real.exp (6 - 3 * Real.pi) =
          Real.exp w * (Real.exp (Real.pi - w - 2) * Real.exp (8 - 4 * Real.pi)) by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
        ring
    _ < 1 / 2 := by
        have h4 : Real.exp (6 - 3 * Real.pi) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
        have h5 : 4 < Real.exp 3 := by linarith [Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)]
        have h7 : Real.exp (-3) < 1 / 4 := by
          rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 3) (by norm_num)]
          linarith
        rw [div_lt_div_iff₀ hpos (by norm_num)]
        linarith

end ReciprocityTheory.ChartRestriction.G.FD
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitative

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitativeHolds

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cusp_coefficient_quantitative_holds : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLineOfCovering

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem isotropic_outside_line_of_covering (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem isotropic_outside_line : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBound

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem shortVectorBound : ShortVectorBound (E := E) :=
  shortVectorBound_of_coefficient_bounds fourier_coefficients_holds cusp_coefficient_quantitative_holds flowCoefficientDecay coefficientIndex_lowerBound coefficientHeight_bound counting_exponential_sum_holds isotropic_outside_line

end ReciprocityTheory.ChartRestriction.G.FD
end
end
