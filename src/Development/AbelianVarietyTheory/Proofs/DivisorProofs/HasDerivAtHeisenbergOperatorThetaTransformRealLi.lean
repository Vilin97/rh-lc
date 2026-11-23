module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZero

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by

      simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by

    simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
    Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  first | exact @GlobalTheory.ThetaTransform.symV_realLine_eq_zero | exact GlobalTheory.ThetaTransform.symV_realLine_eq_zero | (intros; apply GlobalTheory.ThetaTransform.symV_realLine_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) → ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 := by
  first | exact @GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero | exact GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero | (intros; apply GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaDeriv

theorem decay_majorant {F : Type} [Field F] [NumberField F] {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ C : ℝ, ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
      ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]

theorem schr_line_add (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (t h : ℝ) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (M (t + h)) Φ = GlobalTheory.WeilM.schr ψ (M t) (GlobalTheory.WeilM.schr ψ (M h) Φ) := by
  rw [schr_schr, GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add (f := _)]

theorem exists_deriv_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {M : ℝ →+ VA F N} (hM : IsRealLine M) {Φ : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) :
    ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N), ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨f', hf'⟩ := GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg
    exact ⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩
  | zero =>
    refine ⟨0, zero_mem _, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0 := by
      funext s; simp [GlobalTheory.WeilM.schr]
    rw [e]
    exact hasDerivAt_const 0 0
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ', h1m, h1d⟩ := h1
    obtain ⟨Ψ', h2m, h2d⟩ := h2
    refine ⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) =
        fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z := by
      funext s; simp [GlobalTheory.WeilM.schr, mul_add]
    rw [e]
    exact (h1d z).add (h2d z)
  | smul c Φ _ h =>
    obtain ⟨Φ', hm, hd⟩ := h
    refine ⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z := by
      funext s; simp [GlobalTheory.WeilM.schr]; ring
    rw [e]
    exact (hd z).const_mul c

theorem hasDerivAt_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    {Φ Φ' : (Fin N → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0)
    (z : Fin N → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t) := by
    have e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h =>
        ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1) := by
      funext h
      rw [schr_line_add hF ψ hM]
      rfl
    rw [e, sub_self]
    exact (hd (z + (M t).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

end GlobalTheory.ThetaDeriv


open GlobalTheory.ThetaDeriv in
theorem GlobalTheory.ThetaTransform.hasDerivAt_heisV_line : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N),
      ∀ w, HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  intro F _ _ N _ ψ hF hψ Φ hΦ M hM
  obtain ⟨Φ', hΦ'm, hΦ'd⟩ := exists_deriv_schr hF ψ hψ hM hΦ
  refine ⟨Φ', hΦ'm, fun w => ?_⟩
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this
end
end
end
