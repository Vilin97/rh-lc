module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KFiniteVectorsInGeneratedSubmodule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ContinuousDSWOrbit
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JKFinA
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.UrysohnsLemma
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SigLamSmoothOfGenSub
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FinAlgSepKG

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem approx_id {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hsep : (Mult1.Down.KF.finAlg K).SeparatesPoints) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (F : ι → K → E) (hF : ∀ i, Continuous (F i)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ α : C(K, ℂ), Mult1.Down.KF.Fin2 α ∧ ∀ i, ‖∫ k, α k • F i k ∂μ - F i 1‖ < δ := by
  classical
  have hint : ∀ (a : C(K, ℂ)) i, Integrable (fun k => a k • F i k) μ := fun a i =>
    integrableOn_univ.mp ((a.continuous.smul (hF i)).continuousOn.integrableOn_compact isCompact_univ)

  set U : Set K := ⋂ i, {k | ‖F i k - F i 1‖ < δ / 3}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt ((hF i).sub continuous_const).norm continuous_const
  have h1U : (1 : K) ∈ U := mem_iInter.2 fun i => by simp [hδ]

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (1 : K)))
    hU.isClosed_compl (disjoint_singleton_left.2 fun h => h h1U)
  set b : K → ℝ := fun k => 1 - f k
  have hbc : Continuous b := continuous_const.sub f.continuous
  have hb0 : ∀ k, 0 ≤ b k := fun k => by simp only [b]; linarith [(hf01 k).2]
  have hb1 : b 1 = 1 := by simp only [b]; rw [hf0 (mem_singleton 1)]; simp
  have hbU : ∀ k, k ∉ U → b k = 0 := fun k hk => by simp only [b]; rw [hf1 hk]; simp
  have hbcs : HasCompactSupport b := isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  have hcpos : 0 < ∫ k, b k ∂μ :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbcs hb0 (by rw [hb1]; exact one_ne_zero)
  set c := ∫ k, b k ∂μ
  have hbint : Integrable b μ := integrableOn_univ.mp (hbc.continuousOn.integrableOn_compact isCompact_univ)
  set β : C(K, ℂ) := ⟨fun k => ((b k / c : ℝ) : ℂ), Complex.continuous_ofReal.comp (hbc.div_const c)⟩
  have hβ : ∀ i, ‖∫ k, β k • F i k ∂μ - F i 1‖ ≤ δ / 3 := by
    intro i
    have hβ1 : ∫ k, β k • F i 1 ∂μ = F i 1 := by
      rw [integral_smul_const]
      have : ∫ k, β k ∂μ = 1 := by
        show ∫ k, ((b k / c : ℝ) : ℂ) ∂μ = 1
        rw [integral_complex_ofReal, integral_div]
        rw [show ∫ k, b k ∂μ = c from rfl, div_self hcpos.ne', Complex.ofReal_one]
      rw [this, one_smul]
    have hc : Integrable (fun k => β k • F i 1) μ :=
      integrableOn_univ.mp ((β.continuous.smul continuous_const).continuousOn.integrableOn_compact isCompact_univ)
    rw [← hβ1, ← integral_sub (hint β i) hc]
    calc ‖∫ k, (β k • F i k - β k • F i 1) ∂μ‖ ≤ ∫ k, b k / c * (δ / 3) ∂μ := by
          refine norm_integral_le_of_norm_le ((hbint.div_const c).mul_const _) (Filter.Eventually.of_forall fun k => ?_)
          rw [← smul_sub, norm_smul]
          by_cases hk : k ∈ U
          · have := (mem_iInter.1 hk) i
            simp only [mem_ofPred_eq] at this
            have hn : ‖β k‖ = b k / c := by
              show ‖((b k / c : ℝ) : ℂ)‖ = _
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb0 k) hcpos.le)]
            rw [hn]
            exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hb0 k) hcpos.le)
          · have hn : β k = 0 := by show ((b k / c : ℝ) : ℂ) = 0; rw [hbU k hk]; simp
            rw [hn, norm_zero, zero_mul, hbU k hk, zero_div, zero_mul]
      _ = δ / 3 := by
          rw [integral_mul_const, integral_div]
          rw [show (∫ k, b k ∂μ) = c from rfl, div_self hcpos.ne', one_mul]

  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_finsetSum Finset.univ fun i _ => (hF i).norm).continuousOn
  have hMi : ∀ i k, ‖F i k‖ ≤ M := fun i k => by
    have := hM k (mem_univ k)
    rw [Real.norm_eq_abs] at this
    refine le_trans ?_ ((le_abs_self _).trans this)
    exact Finset.single_le_sum (f := fun i => ‖F i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  set R := |M| * μ.real univ + 1
  have hR : 0 < R := by positivity
  have hη : 0 < δ / 3 / R := by positivity
  have hmem : β ∈ closure ((Mult1.Down.KF.finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
    have : β ∈ (Mult1.Down.KF.finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨α, hα, hαβ⟩ := Metric.mem_closure_iff.1 hmem _ hη
  refine ⟨α, hα, fun i => ?_⟩
  have hdiff : ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ ≤ δ / 3 / R * |M| * μ.real univ := by
    rw [← integral_sub (hint α i) (hint β i)]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [← sub_smul, norm_smul]
    have h1 : ‖α k - β k‖ ≤ δ / 3 / R := by
      have := (β - α).norm_coe_le_norm k
      rw [dist_eq_norm] at hαβ
      rw [norm_sub_rev]
      exact this.trans hαβ.le
    exact mul_le_mul h1 ((hMi i k).trans (le_abs_self M)) (norm_nonneg _) hη.le
  have hsmall : δ / 3 / R * |M| * μ.real univ < δ / 3 := by
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hR]
    have : |M| * μ.real univ < R := by simp [R]
    nlinarith [measureReal_nonneg (μ := μ) (s := univ), abs_nonneg M]
  calc ‖∫ k, α k • F i k ∂μ - F i 1‖
      ≤ ‖∫ k, α k • F i k ∂μ - ∫ k, β k • F i k ∂μ‖ + ‖∫ k, β k • F i k ∂μ - F i 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 3 + δ / 3 := add_lt_add_of_lt_of_le (hdiff.trans_lt hsmall) (hβ i)
    _ < δ := by linarith

theorem finAlg_sep_KG {n : ℕ} (ε : Fin n → Bool) : (Mult1.Down.KF.finAlg (S7.KG ε)).SeparatesPoints := by
  intro k k' hne
  have hne' : S7.toMK k ≠ S7.toMK k' := fun h => hne (Subtype.ext (Subtype.ext (Units.ext h)))
  obtain ⟨i, j, hij⟩ : ∃ i j, S7.toMK k i j ≠ S7.toMK k' i j := by
    by_contra hc
    push Not at hc
    exact hne' (Matrix.ext hc)
  have hcont : ∀ a b : Fin n, Continuous fun κ : S7.KG ε => S7.toMK κ a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp S7.IdA.continuous_toMK)
  refine ⟨_, ⟨⟨fun κ => S7.toMK κ i j, hcont i j⟩, ?_, rfl⟩, hij⟩
  refine ⟨Fin n, inferInstance, fun l k₀ => S7.toMK k₀ i l, fun l => ⟨fun κ => S7.toMK κ l j, hcont l j⟩,
    fun k₀ κ => ?_⟩
  show (S7.toMK k₀ * S7.toMK κ) i j = _
  rw [Matrix.mul_apply]
  rfl

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KernelCondition

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_kfin_near {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x : Hlam ε Ψ v₀, Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x ∧ nuJ (sigLam ε Ψ v₀) Ws (u - x) < e := by
  have := S7.compactSpace_KG ε
  have : MeasureTheory.IsFiniteMeasure (S7.muK ε) := by unfold S7.muK; infer_instance
  have : (S7.muK ε).IsOpenPosMeasure := by unfold S7.muK; infer_instance
  have hσ : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWg : ∀ i : Fin Ws.length, ∀ X ∈ Ws.get i, inG ε X := fun i => hWs _ (List.get_mem Ws i)
  obtain ⟨α, hα, hαF⟩ := approx_id (S7.muK ε) (finAlg_sep_KG ε)
    (fun (i : Fin Ws.length) (k : S7.KG ε) => dSW (sigLam ε Ψ v₀) (Ws.get i) (sigLam ε Ψ v₀ (S7.toMK k) u))
    (fun i => continuous_dSW_orbit hσ (hWg i) hu) (δ := e / (Ws.length + 1)) (by positivity)
  obtain ⟨x, hxdef⟩ : ∃ x : Hlam ε Ψ v₀, x = ∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε) := ⟨_, rfl⟩
  have hK : Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x := by rw [hxdef]; exact kfin_integral hσ u hα
  obtain ⟨y, -, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hK
  have hxs : IsSmoothVecU ε (sigLam ε Ψ v₀) x := by
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
    have h := sigLam_smooth_of_genSub (Ψ := Ψ) (v₀ := v₀) hyH
    rwa [show (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x from Subtype.ext hyx] at h
  refine ⟨x, hK, ?_⟩
  have hterm : ∀ w ∈ Ws, ‖dSW (sigLam ε Ψ v₀) w (u - x)‖ ≤ e / (Ws.length + 1) := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hw
    have hxs' : IsSmoothVecU ε (sigLam ε Ψ v₀) (∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε)) := by
      rw [← hxdef]; exact hxs
    rw [dSW_sub hσ (hWg i) hu hxs, hxdef]
    erw [dSW_integral hσ (fun z hz => sigLam_sep z hz) (hWg i) hu α hxs']
    rw [norm_sub_rev]
    have h1 : sigLam ε Ψ v₀ (S7.toMK (1 : S7.KG ε)) u = u := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    have h2 := hαF i
    beta_reduce at h2
    rw [h1] at h2
    exact h2.le
  unfold nuJ
  calc (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).sum
      ≤ (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).length • (e / (Ws.length + 1)) :=
        List.sum_le_card_nsmul _ _ fun r hr => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
          exact hterm w hw
    _ = (Ws.length : ℝ) * (e / (Ws.length + 1)) := by rw [List.length_map, nsmul_eq_mul]
    _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ExistsNearSmooth

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_near_smooth {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∃ hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀,
        nuJ (sigLam ε Ψ v₀) Ws (u - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) < e := by
  obtain ⟨x, hxK, hxe⟩ := exists_kfin_near hlam hgap hP hv₀ Ws hWs u hu he
  obtain ⟨y, hy, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hxK
  have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
  refine ⟨y, hy, hyH, ?_⟩
  have hxy : (⟨((y : smD ε (rreg ε)) : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x := Subtype.ext hyx
  rw [hxy]
  exact hxe

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end
