module

public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecay

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

open scoped ContDiff

namespace GlobalTheory.FourierSndDecay

lemma norm_iteratedFDeriv_slice_le {U V : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : SchwartzMap (U × V) ℂ) (u : U) (q : ℕ) (t : V) :
    ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ ‖iteratedFDeriv ℝ q h (u, t)‖ := by
  have c0 : ContDiff ℝ ∞ h := h.smooth'
  have e : (fun s : V => h (u, s)) =
      (fun x : U × V => h (x + (u, 0))) ∘ (ContinuousLinearMap.inr ℝ U V) := by
    funext s; simp
  have ct : ContDiff ℝ ∞ (fun x : U × V => h (x + (u, 0))) :=
    c0.comp (contDiff_id.add contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ ct t (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin q, ‖(ContinuousLinearMap.inr ℝ U V)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ U V)
  have : ContinuousLinearMap.inr ℝ U V t + (u, 0) = (u, t) := by simp
  rw [this]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

lemma one_add_pow_le_two_pow_mul (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ n ≤ 1 + t ^ n := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht n]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht n]
  calc (1 + t) ^ n ≤ (2 * max 1 t) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = 2 ^ n * (max 1 t) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + t ^ n) := by gcongr

theorem fourier_snd_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ,
    ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  intro U V _ _ _ _ _ _ _ _ h k
  set d := Module.finrank ℝ V with hd
  set N := k + (d + 1) with hN
  set S := 2 ^ N * ((Finset.Iic (N, k)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hSdef
  set I := ∫ t : V, (1 + ‖t‖) ^ (-((d : ℝ) + 1)) with hIdef
  have hint : Integrable (fun t : V => (1 + ‖t‖) ^ (-((d : ℝ) + 1))) :=
    integrable_one_add_norm (by linarith)
  have hpt : ∀ (u : U) (t : V) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        ≤ S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) := by
    intro u t q hq
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, k)) (k := N) (n := q)
      le_rfl hq h (u, t)
    have hu : ‖u‖ ≤ ‖(u, t)‖ := norm_fst_le (u, t)
    have ht : ‖t‖ ≤ ‖(u, t)‖ := norm_snd_le (u, t)
    have hpos : 0 < (1 + ‖t‖) ^ ((d : ℝ) + 1) := by positivity
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    have e : (1 + ‖t‖) ^ ((d : ℝ) + 1) = (1 + ‖t‖) ^ (d + 1) := by
      rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e]
    calc (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ * (1 + ‖t‖) ^ (d + 1)
        ≤ (1 + ‖(u, t)‖) ^ k * ‖iteratedFDeriv ℝ q h (u, t)‖ * (1 + ‖(u, t)‖) ^ (d + 1) := by
          gcongr; exact norm_iteratedFDeriv_slice_le h u q t
      _ = (1 + ‖(u, t)‖) ^ N * ‖iteratedFDeriv ℝ q h (u, t)‖ := by rw [hN, pow_add]; ring
      _ ≤ S := hS
  have hcd : ∀ u : U, ContDiff ℝ ∞ (fun s : V => h (u, s)) := fun u =>
    h.smooth'.comp (contDiff_const.prodMk contDiff_id)
  have hintq : ∀ (u : U) (q : ℕ), q ≤ k →
      Integrable (fun t => ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖) := by
    intro u q hq
    refine (hint.const_mul S).mono'
      ((hcd u).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have := hpt u t q hq
    have h1 : 1 ≤ (1 + ‖u‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg u])
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (fun s : V => h (u, s)) t)]
  have hintb : ∀ (u : U) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ S * I := by
    intro u q hq
    calc (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        = ∫ t, (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ t : V, S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) :=
          integral_mono ((hintq u q hq).const_mul _) (hint.const_mul S) (fun t => hpt u t q hq)
      _ = S * I := integral_const_mul _ _
  have hF : ∀ (u : U) (w : V) (n : ℕ), n ≤ k →
      (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖) ≤ 2 ^ n * ((n + 1) * (S * I)) := by
    intro u w n hn
    have h'f : ∀ (k' m : ℕ), (k' : ℕ∞) ≤ 0 → (m : ℕ∞) ≤ (n : ℕ∞) →
        Integrable (fun v : V => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m (fun s : V => h (u, s)) v‖) := by
      intro k' m hk' hm
      have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
      have hmn : m ≤ n := by exact_mod_cast hm
      subst hk0
      simpa using hintq u m (hmn.trans hn)
    have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := fun t : V => h (u, t)) (K := 0)
      (N := n) ((hcd u).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := n) le_rfl le_rfl w
    have hsum : (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun s : V => h (u, s)) v‖)
        = ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖ := by
      rw [Finset.sum_product]; simp
    rw [hsum, norm_iteratedFDeriv_zero] at key
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
    have hsb : (1 + ‖u‖) ^ k *
        ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
        ≤ (n + 1) * (S * I) := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ Finset.range (n + 1),
            (1 + ‖u‖) ^ k * ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
          ≤ ∑ _j ∈ Finset.range (n + 1), S * I := Finset.sum_le_sum fun j hj =>
            hintb u j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)
        _ = (n + 1) * (S * I) := by simp
    have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
    calc (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖)
        ≤ (1 + ‖u‖) ^ k * (2 ^ n * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) :=
          mul_le_mul_of_nonneg_left key hu0
      _ = 2 ^ n * ((1 + ‖u‖) ^ k * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) := by ring
      _ ≤ 2 ^ n * ((n + 1) * (S * I)) := by gcongr
  refine ⟨2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))), fun u w => ?_⟩
  have h0 := hF u w 0 (Nat.zero_le _)
  have hk := hF u w k le_rfl
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at h0
  have hw := one_add_pow_le_two_pow_mul ‖w‖ (norm_nonneg _) k
  have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
  calc (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
      ≤ (1 + ‖u‖) ^ k * (2 ^ k * (1 + ‖w‖ ^ k)) * ‖𝓕 (fun t : V => h (u, t)) w‖ := by gcongr
    _ = 2 ^ k * ((1 + ‖u‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
          + (1 + ‖u‖) ^ k * (‖w‖ ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖)) := by ring
    _ ≤ 2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))) := by gcongr

end GlobalTheory.FourierSndDecay
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecayStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

theorem _root_.GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ, ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  first | exact @GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | exact GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | (intros; apply GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPair

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.PartialFourierSum

open GroundTheory.Global NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adelicFourierPi_mul (f : (κ → mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ → AdeleRing (𝓞 F) F) :
    adelicFourierPi F (fun x => f (infPartPi x) * g (finPartPi x)) y =
      mixedFourierPi F f (infPartPi y) * finiteFourierPi F g (finPartPi y) := by
  have h := integral_prod_mul (μ := mixedMeasurePi F) (ν := finiteMeasurePi F)
    (fun u ↦ 𝐞 (-mixedPairingPi F u (infPartPi y)) • f u)
    (fun v ↦ g v * (finiteAdelicChar F (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi F)
    (f := splitEquivPi F κ) (fun p : (κ → mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) ↦
      (𝐞 (-mixedPairingPi F p.1 (infPartPi y)) • f p.1) *
        (g p.2 * (finiteAdelicChar F (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [mixedFourierPi, finiteFourierPi, ← h, ← e, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def, smul_eq_mul]
  ring

theorem exists_summable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (κ → mixedSpace F) ≃L[ℝ] E)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Summable fun ξ : κ → F => ((1 + ‖L (embPi F ξ)‖) ^ k)⁻¹ *
      ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ := by
  obtain ⟨k₀, M, hM, hb⟩ := GlobalTheory.SchwartzMajorant.exists_majorant_pureA F (g := g) hg 0
  refine ⟨k₀, fun k hk => ?_⟩
  set c : ℝ := ‖(L.symm : E →L[ℝ] (κ → mixedSpace F))‖ with hc
  have hn : ∀ v, ‖((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ)‖ = ((1 + ‖L v‖) ^ k)⁻¹ := fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb' := hb 1 (c ^ k₀) (fun v => ((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ))
    (fun v => by
      rw [hn]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (L v)])))
    (fun v => by
      rw [hn, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h1 : ‖v‖ ≤ c * ‖L v‖ := by
        simpa using (L.symm : E →L[ℝ] (κ → mixedSpace F)).le_opNorm (L v)
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖v‖ ^ k₀ ≤ (c * (1 + ‖L v‖)) ^ k₀ :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans (by nlinarith [norm_nonneg (L v)])) _
        _ = c ^ k₀ * (1 + ‖L v‖) ^ k₀ := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg (L v)]) hk) (by positivity))
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) (hM.mul_left (1 + c ^ k₀))
  have h := hb' ξ
  rw [GlobalTheory.SchwartzMajorant.pureA_add_algebraMap, norm_mul, hn] at h
  have e1 : ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((0 : κ → AdeleRing (𝓞 F) F) j).1) = embPi F ξ := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, embPi]
    rw [show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl, map_zero, add_zero]
  have e2 : ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j =>
      ((0 : κ → AdeleRing (𝓞 F) F) j).2) = fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j) := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [show (0 : AdeleRing (𝓞 F) F).2 = 0 from rfl, add_zero]
  rw [e1, e2] at h
  exact h

def shear : ((κ → mixedSpace F) × EuclidPi F κ) ≃L[ℝ] (κ ⊕ κ → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => Sum.elim ((toEuclidPi F).symm p.2 + p.1) ((toEuclidPi F).symm p.2)
      map_add' := fun p q => by
        funext i
        rcases i with i | i
        · simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Sum.elim_inl, Pi.add_apply]; abel
        · simp only [Prod.snd_add, map_add (f := _), Sum.elim_inr, Pi.add_apply]
      map_smul' := fun a p => by
        funext i
        rcases i with i | i
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
            RingHom.id_apply, smul_add]
        · simp only [Prod.smul_snd, map_smul, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      invFun := fun x => (fun i => x (Sum.inl i) - x (Sum.inr i), toEuclidPi F fun i => x (Sum.inr i))
      left_inv := fun p => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; abel
        · simp only [Sum.elim_inr]
          exact (toEuclidPi F).apply_symm_apply p.2
      right_inv := fun x => by
        funext i
        rcases i with i | i
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inr] }

theorem arch_bound (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ u v : κ → mixedSpace F, ‖mixedFourierPi F (fun t => f (Sum.elim (t + u) t)) v‖ ≤
      C * (((1 + ‖u‖) ^ k)⁻¹ * ((1 + ‖toEuclidPiConj F v‖) ^ k)⁻¹) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay (κ → mixedSpace F) (EuclidPi F κ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (shear (F := F) (κ := κ)) f) k
  refine ⟨C, fun u v => ?_⟩
  have h := hC u (toEuclidPiConj F v)
  rw [mixedFourierPi_eq, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem finiteTensor_shift (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)
    (u t : κ → FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (t + u) t) =
      finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) u *
        finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) t := by
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [cosetIndicator_apply]
  by_cases h : t i - b (Sum.inr i) ∈ idealFiniteAdeles J
  · have : t i + u i - b (Sum.inl i) ∈ idealFiniteAdeles J ↔
        u i - (b (Sum.inl i) - b (Sum.inr i)) ∈ idealFiniteAdeles J := by
      rw [show t i + u i - b (Sum.inl i) = (t i - b (Sum.inr i)) + (u i - (b (Sum.inl i) - b (Sum.inr i))) by ring]
      exact AddSubgroup.add_mem_cancel_left _ h
    simp only [this]
  · simp only [if_neg h, mul_zero]

theorem summable_gen (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F =>
      schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  set g₁ := finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) with hg₁
  set g₂ := finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) with hg₂
  have m₁ : g₁ ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _
  have m₂ : finiteFourierPi F g₂ ∈ finiteSchwartzBruhatPi F :=
    finiteFourierPi_mem (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _)
  obtain ⟨k₁, h₁⟩ := exists_summable (ContinuousLinearEquiv.refl ℝ (κ → mixedSpace F)) m₁
  obtain ⟨k₂, h₂⟩ := exists_summable (toEuclidPiConj F) m₂
  obtain ⟨C, hC⟩ := arch_bound f (max k₁ k₂)
  have hs := ((h₁ _ (le_max_left k₁ k₂)).mul_of_nonneg (h₂ _ (le_max_right k₁ k₂))
    (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) hs
  have key : (fun t : κ → AF F => schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) =
      fun t => (fun s => f (Sum.elim (s + embPi F uv.1) s)) (infPartPi t) *
        (g₁ (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) • g₂) (finPartPi t) := by
    funext t
    have e1 : infPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (infPartPi t + embPi F uv.1) (infPartPi t) := by
      rw [← infPartPi_algebraMap]
      funext i
      rcases i with i | i
      · simp only [infPartPi, Sum.elim_inl, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      · rfl
    have e2 : finPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (finPartPi t + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) (finPartPi t) := by
      rw [← finPartPi_algebraMap]
      funext i
      rcases i with i | i <;> rfl
    rw [schwartzBruhatTensorPi, e1, e2, finiteTensor_shift]
    rfl
  rw [key, adelicFourierPi_mul (fun s => f (Sum.elim (s + embPi F uv.1) s)), finiteFourierPi_smul, infPartPi_algebraMap, finPartPi_algebraMap, norm_mul,
    Pi.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_right (hC _ _) (by positivity)).trans (le_of_eq ?_)
  simp only [ContinuousLinearEquiv.refl_apply]
  ring

theorem summable_partial_fourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  intro F _ _ κ _ φ hφ
  have hS : schA F (κ ⊕ κ) = cosetSpanPi F (κ ⊕ κ) := by
    rw [← schwartzBruhatPi_eq_cosetSpanPi]
    refine congrArg (Submodule.span ℂ) (Set.ext fun Φ => ?_)
    exact ⟨fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩, fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩⟩
  have hI : ∀ ψ ∈ cosetSpanPi F (κ ⊕ κ), ∀ u : κ → AF F,
      Integrable (fun t : κ → AF F => ψ (Sum.elim (t + u) t)) (adeleMeasurePi F) := fun ψ hψ u =>
    integrable_of_mem_schwartzBruhatPi (GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi F κ ψ (hS ▸ hψ) u)
  rw [hS] at hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact summable_gen f J b
  | zero =>
    simp only [Pi.zero_apply, adelicFourierPi, zero_mul, integral_zero, norm_zero]
    exact summable_zero
  | add G H hG hH ihG ihH =>
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) (ihG.add ihH)
    have h := congrFun (adelicFourierPi_add (hI G hG fun i => algebraMap F (AF F) (uv.1 i))
      (hI H hH fun i => algebraMap F (AF F) (uv.1 i))) (fun i => algebraMap F (AF F) (uv.2 i))
    exact (congrArg norm h).le.trans (norm_add_le _ _)
  | smul c G _ ih =>
    refine (ih.mul_left ‖c‖).congr fun uv => ?_
    have h := congrFun (adelicFourierPi_smul c (fun t : κ → AF F =>
      G (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))) (fun i => algebraMap F (AF F) (uv.2 i))
    rw [← _root_.norm_smul]
    exact (congrArg norm h).symm

end GlobalTheory.PartialFourierSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPairStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

theorem _root_.GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  first | exact @GlobalTheory.PartialFourierSum.summable_partial_fourier | exact GlobalTheory.PartialFourierSum.summable_partial_fourier | (intros; apply GlobalTheory.PartialFourierSum.summable_partial_fourier <;> assumption)
end
end
