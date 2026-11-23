module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
public import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.HcMultDSOfAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyEqZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.HasDerivAtDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.ImInnerSelf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Algebra.Group.Units
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.OneParamHasDerivAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.HasDerivAtDS
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.IntegralSumCoef

section

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CoefficientIntegrals

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem re_coef_ge {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {g : UJ ε} {v : H} (hv : ‖v‖ = 1)
    (h : ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2) : (1 / 2 : ℝ) ≤ (coefOn σ v v g).re := by
  have h1 : coefOn σ v v g = ⟪v, v⟫_ℂ + ⟪v, σ (umat g) v - v⟫_ℂ := by
    simp [coefOn]
  have h2 : ‖⟪v, σ (umat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
    calc _ ≤ ‖v‖ * ‖σ (umat g) v - v‖ := norm_inner_le_norm _ _
      _ ≤ 1 / 2 := by rw [hv] at h ⊢; linarith
  have h4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h2)).1
  have h5 : (⟪v, v⟫_ℂ).re = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hv] at this
    simpa using this
  rw [h1, Complex.add_re, h5]
  linarith

def sumCoef {ι : Type} [Fintype ι] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : ι → H) (g : UJ ε) : ℂ :=
  ∑ i, coefOn σ (v i) (v i) g

theorem re_sumCoef_ge {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) {g : UJ ε}
    (hg : ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2) :
    (Fintype.card ι : ℝ) / 2 ≤ (sumCoef σ v g).re := by
  unfold sumCoef
  rw [Complex.re_sum]
  have hi : ∀ i, (1 / 2 : ℝ) ≤ (coefOn σ (v i) (v i) g).re := fun i =>
    re_coef_ge (hv.1 i) (hg _ (hW i))
  calc (Fintype.card ι : ℝ) / 2 = ∑ _i : ι, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

theorem integral_sumCoef {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {d : ℝ} (hd : IsFdeg (muG ε) σ d) {v : ι → H} (hv : Orthonormal ℂ v) :
    Integrable (fun g => sumCoef σ v g * star (sumCoef σ v g)) (muG ε) ∧
      ∫ g, sumCoef σ v g * star (sumCoef σ v g) ∂(muG ε) = (Fintype.card ι : ℂ) / (d : ℂ) := by
  have hexp : (fun g : UJ ε => sumCoef σ v g * star (sumCoef σ v g)) = fun g =>
      ∑ i, ∑ j, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) := by
    funext g
    unfold sumCoef
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hint : ∀ i j, Integrable
      (fun g => coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)) (muG ε) :=
    fun i j => (hd.2 _ _ _ _).1
  have hij : ∀ i j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) =
      if i = j then 1 / (d : ℂ) else 0 := by
    intro i j
    rw [(hd.2 _ _ _ _).2, orthonormal_iff_ite.mp hv j i, orthonormal_iff_ite.mp hv i j]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  · rw [hexp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    calc _ = ∑ i, ∑ j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_finsetSum _ fun j _ => hint i j
      _ = _ := by
          simp only [hij, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring

theorem card_le {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (muG ε) σ d) {W : Submodule ℂ H} {K : Set (UJ ε)} (hKm : MeasurableSet K)
    (hKf : muG ε K ≠ ⊤) (hKpos : 0 < (muG ε).real K)
    (hK : ∀ g ∈ K, ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2)
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) :
    (Fintype.card ι : ℝ) ≤ 4 / (d * (muG ε).real K) := by
  classical
  set m := (Fintype.card ι : ℝ) with hmdef
  obtain ⟨hint, hval⟩ := integral_sumCoef hd hv
  let f : UJ ε → ℝ := fun g => (sumCoef σ v g * star (sumCoef σ v g)).re
  have hfint : Integrable f (muG ε) := hint.re
  have hfn : ∀ g, f g = Complex.normSq (sumCoef σ v g) := fun g => by
    simp [f, Complex.mul_conj]
  have hf0 : ∀ g, 0 ≤ f g := fun g => by rw [hfn]; exact Complex.normSq_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have hK' : ∀ g ∈ K, (m / 2) ^ 2 ≤ f g := by
    intro g hg
    have h1 := re_sumCoef_ge hv hW (hK g hg)
    rw [hfn, Complex.normSq_apply]
    nlinarith [sq_nonneg (sumCoef σ v g).im]
  have hset : (m / 2) ^ 2 * (muG ε).real K ≤ ∫ g in K, f g ∂(muG ε) :=
    by
      have := setIntegral_ge_of_const_le hKm hKf hK' hfint.integrableOn
      rwa [smul_eq_mul, mul_comm] at this
  have hle : ∫ g in K, f g ∂(muG ε) ≤ ∫ g, f g ∂(muG ε) :=
    setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0)
  have htot : ∫ g, f g ∂(muG ε) = m / d := by
    show ∫ g, (sumCoef σ v g * star (sumCoef σ v g)).re ∂(muG ε) = m / d
    have hc : ((Fintype.card ι : ℂ) / (d : ℂ)) = ((m / d : ℝ) : ℂ) := by
      rw [hmdef]
      push_cast
      ring
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [hr, hval, hc, Complex.ofReal_re]
  have hd0 := hd.1
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]
    exact div_nonneg (by norm_num) (mul_pos hd0 hKpos).le
  · rw [le_div_iff₀ (mul_pos hd0 hKpos)]
    have hA : (m / 2) ^ 2 * (muG ε).real K ≤ m / d := (hset.trans hle).trans_eq htot
    have hB : (m / 2) ^ 2 * (muG ε).real K * d ≤ m := by
      have := mul_le_mul_of_nonneg_right hA hd0.le
      rwa [div_mul_cancel₀ _ hd0.ne'] at this
    nlinarith [hB, hpos, mul_pos hd0 hKpos]

end CoefficientIntegrals

open CoefficientIntegrals in
theorem c7 : FormalDegreeFiniteDim := by
  intro n ε H _ _ _ σ _ d hd W U hU hUW
  classical
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKf : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < (muG ε).real K :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne' hKf
  have hbound : ∀ (m : ℕ) (v : Fin m → H), Orthonormal ℂ v → (∀ i, v i ∈ W) →
      (m : ℝ) ≤ 4 / (d * (muG ε).real K) := by
    intro m v hv hvW
    simpa using card_le hd hKm hKf hKpos (fun g hg => hUW g (hKU hg)) hv hvW
  by_contra hfin
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / (d * (muG ε).real K))
  let bW := Module.Basis.ofVectorSpace ℂ W
  have hI : (Module.Basis.ofVectorSpaceIndex ℂ W).Infinite := by
    intro hfinI
    haveI : Finite (Module.Basis.ofVectorSpaceIndex ℂ W) := hfinI.to_subtype
    exact hfin (Module.Finite.of_basis bW)
  obtain ⟨t, htsub, htcard⟩ := hI.exists_subset_card_eq m
  let u : t → W := fun x => bW ⟨x.1, htsub x.2⟩
  have hu : LinearIndependent ℂ u :=
    bW.linearIndependent.comp _ (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  let F : Submodule ℂ W := Submodule.span ℂ (Set.range u)
  haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hF : Module.finrank ℂ F = m := by
    rw [finrank_span_eq_card hu]
    simp [htcard]
  let ob := stdOrthonormalBasis ℂ F
  let v : Fin (Module.finrank ℂ F) → H := fun i => ((ob i : F) : W)
  have hv : Orthonormal ℂ v :=
    (ob.orthonormal.comp_linearIsometry F.subtypeₗᵢ).comp_linearIsometry W.subtypeₗᵢ
  have h := hbound _ v hv (fun i => ((ob i : F) : W).2)
  rw [hF] at h
  linarith

end Formalism.L2.SG.Pf.admitted
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.KavgFixRange

section

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ExponentialDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kavg_fix_range {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) (Θ : S →ₗ[ℂ] H)
    (hΘ : ∀ (a : KG ε) (v w : S), (w : H) = σ (toMK a) v → Θ w = σ (toMK a) (Θ v)) (s : S) :
    kavg hσ he (Θ s) = Θ s := by
  have hs : kavg hσ he (s : H) = s := hfix s s.2
  have hval : ∀ x : H, kavg hσ he x = ∫ k, e k • σ (toMK k) x ∂muK ε := fun x => by
    unfold Formalism.MainNotions.BridgeCPX.kavg
    rfl
  have hkS : ∀ k : KG ε, σ (toMK k) s ∈ S := fun k => hst _ k.2 _ s.2
  let F : KG ε → S := fun k => e k • ⟨σ (toMK k) s, hkS k⟩
  have hΘF : ∀ k, Θ (F k) = e k • σ (toMK k) (Θ s) := fun k => by
    simp only [F, map_smul]
    rw [hΘ k s ⟨σ (toMK k) s, hkS k⟩ rfl]
  have hsub : ((∫ k, F k ∂muK ε : S) : H) = ∫ k, (F k : H) ∂muK ε :=
    (S.subtypeₗᵢ.integral_comp_comm F).symm
  have hint : (∫ k, F k ∂muK ε) = s := by
    apply Subtype.ext
    rw [hsub, ← hs, hval]
    rfl
  rw [hval, integral_congr_ae (Filter.Eventually.of_forall fun k => (hΘF k).symm)]
  by_cases hFi : Integrable F (muK ε)
  · have h := (LinearMap.toContinuousLinearMap Θ).integral_comp_comm hFi
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [h, hint]
  · rw [integral_undef hFi] at hint
    subst hint
    have h0 : ∀ k, F k = 0 := fun k => by
      ext
      simp [F]
    simp only [h0, map_zero, integral_zero]

theorem kavg_fix_isoK {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) {v : H} (hv : v ∈ isoK ε σ S) :
    kavg hσ he v = v := by
  have hle : isoK ε σ S ≤ LinearMap.ker
      ((((kavg hσ he : H →L[ℂ] H) - ContinuousLinearMap.id ℂ H : H →L[ℂ] H)) : H →ₗ[ℂ] H) := by
    refine sSup_le ?_
    rintro T ⟨Θ, hΘ, rfl⟩
    rintro x ⟨s, rfl⟩
    simp [LinearMap.mem_ker, sub_eq_zero, kavg_fix_range hσ hst he hfix Θ hΘ s]
  have h := hle hv
  simpa [LinearMap.mem_ker, sub_eq_zero] using h

end ExponentialDecomposition

theorem c0 : SmoothVectorsDense := by
  intro n ε H _ _ _ σ hσ hirr w hw S hfd hst v hv
  obtain ⟨e, he, hfix, hrange⟩ := compactProj (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  have hfix' : ∀ x ∈ S, kavg hσ he x = x := fun x hx => by
    rw [kavg_apply]
    exact hfix x hx
  have hE : kavg hσ he v = v := ExponentialDecomposition.kavg_fix_isoK hσ hst he hfix' hv
  have hvc : v ∈ closure (Vsub ε hσ w : Set H) := by
    have h := Vsub_dense hσ hirr hw
    have h2 : v ∈ (Vsub ε hσ w).topologicalClosure := by
      rw [h]
      trivial
    exact h2
  have h3 : kavg hσ he v ∈ closure ((Vsub ε hσ w ⊓ isoK ε σ S : Submodule ℂ H) : Set H) := by
    refine map_mem_closure (kavg hσ he).continuous hvc ?_
    rintro _ ⟨Φ, hΦ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_inf]
    refine ⟨⟨kconv ε e Φ, test_kconv he hΦ, kavg_vec hσ w he hΦ⟩, ?_⟩
    rw [kavg_apply]
    exact hrange _
  rwa [hE] at h3

end Formalism.L2.SG.Pf.admitted
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.SgCases

section

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GeneratorWeights

variable {n : ℕ}

theorem sg_cases (ε : Fin n → Bool) (p : Fin n × Fin n) : sg ε p = 1 ∨ sg ε p = -1 := by
  unfold sg
  split_ifs <;> simp

theorem wt_ge (p : Fin n × Fin n) : 1 / 2 ≤ wt p := by
  unfold wt
  split_ifs <;> norm_num

theorem wt_le (p : Fin n × Fin n) : wt p ≤ 1 := by
  unfold wt
  split_ifs <;> norm_num

theorem gen_mem (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (gen ε p) := by
  apply Formalism.L2.SG.Pf.admitted.AdmissibleVectors.inG_gen <;> assumption

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem sum_eq (hC : Calc ε σ D) {c : ℝ} (hc : ∀ v ∈ D, Cas ε σ v = (c : ℂ) • v) {v : H} (hv : v ∈ D) :
    ∑ p : Fin n × Fin n, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 = c * ‖v‖ ^ 2 := by
  have hgen : ∀ p, inG ε (gen ε p) := gen_mem ε
  have key : ⟪Cas ε σ v, v⟫_ℂ =
      ∑ p, ((wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    unfold Cas
    rw [inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_smul_left, hC.skew _ (hgen p) _ (hC.mem _ (hgen p) v hv) v hv,
      inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have h2 : ((c * ‖v‖ ^ 2 : ℝ) : ℂ) =
      ((∑ p, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← key, hc v hv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  exact (Complex.ofReal_inj.1 h2).symm

end GeneratorWeights

open GeneratorWeights in
theorem c4 : CasimirScalarBounded := by
  intro n ε H _ _ _ σ D hC c hc W C hW
  set K : ℝ := 2 * ((Fintype.card (Fin n × Fin n) : ℝ) * C ^ 2 + |c|) with hK
  refine ⟨max C (Real.sqrt K), fun p v hvD hvW => ?_⟩
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  by_cases hp : ε p.1 = ε p.2
  · exact (hW p hp v hvW).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)
  · have hsum := sum_eq hC hc hvD
    have hsgp : sg ε p = -1 := by simp [sg, hp]
    have hterm : ∀ q, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
      intro q
      have h3 := wt_le q
      have h4 := wt_ge q
      rcases sg_cases ε q with h | h
      · have hq : ε q.1 = ε q.2 := by
          by_contra hne
          simp [sg, hne] at h
          norm_num at h
        have h1 := hW q hq v hvW
        have h2 : ‖dS σ (gen ε q) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [h, mul_one]
        have h5 : wt q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ 1 * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        nlinarith [h2, h5]
      · rw [h]
        have h5 : 0 ≤ wt q * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        nlinarith [sq_nonneg (C * ‖v‖), h5]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun q => wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2) (Finset.mem_univ p)
    have hrest : ∑ q ∈ Finset.univ.erase p, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤
        (Fintype.card (Fin n × Fin n) : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
      calc _ ≤ ∑ q ∈ Finset.univ.erase p, C ^ 2 * ‖v‖ ^ 2 :=
            Finset.sum_le_sum fun q _ => hterm q
        _ = ((Finset.univ.erase p).card : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ)))
            (by positivity)
    have hwp := wt_ge p
    rw [hsgp] at hsplit
    have e2 : (1 / 2) * ‖dS σ (gen ε p) v‖ ^ 2 ≤ wt p * ‖dS σ (gen ε p) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwp (sq_nonneg _)
    have e3 : -c * ‖v‖ ^ 2 ≤ |c| * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg _)
    have hsq : ‖dS σ (gen ε p) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
      rw [hK]
      nlinarith [hsplit, hsum, hrest, e2, e3]
    have hK0 : 0 ≤ K := by positivity
    have hle : ‖dS σ (gen ε p) v‖ ≤ Real.sqrt K * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (dS σ (gen ε p) v)), ← Real.sqrt_sq hv0,
        ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt hsq
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)

end Formalism.L2.SG.Pf.admitted
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.KFinSmooth

section

@[expose] public section

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.admitted

theorem hcMultDS : Formalism.MainNotions.BridgeCPX.HCMultDS :=
  hcMultDS_of_all c0 c1 c2 c3 c4 c5 c6 c7

theorem hcAdmDS : Formalism.MainNotions.BridgeCPX.HCAdmDS := hcAdmDS_of hcMultDS

theorem kFinSmooth : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth := kFinSmooth_of hcMultDS

theorem kFinSmooth' : Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth := kFinSmooth_of' hcMultDS

end Formalism.L2.SG.Pf.admitted
end
end
