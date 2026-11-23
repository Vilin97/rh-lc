module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.Lemmas
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.HkIterContOn
import Aesop.Main
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.Lemmas
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemBound

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Analytic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem lem_nrm (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ A : HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ,
    ‖A‖ ^ 2 ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      (A fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  refine ⟨‖Ψ‖ ^ 2, sq_nonneg _, fun A => ?_⟩
  have h1 := Ψ.le_opNorm (fun v => A fun i => Module.finBasis ℝ (HS L N) (v i))
  rw [hΨ] at h1
  calc ‖A‖ ^ 2 ≤ (‖Ψ‖ * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖Ψ‖ ^ 2 * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_sum _) (sq_nonneg _)

theorem lem_meas {k : ℕ} (d : Dom L N) {ω₁ : Form (HS L N) (k + 1)} (h1 : ContinuousOn ω₁ (Pos L N)) :
    AEStronglyMeasurable (fun x => fr ω₁ (ofS L N x)) (d.μ.restrict d.D) := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  have hc : Continuous fun x => fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
      fr ω₁ (ofS L N x) fun i => Module.finBasis ℝ (HS L N) (v i) :=
    continuous_pi fun v => (fr_comp_cont h1 _).comp ofS_cont
  have := Ψ.continuous.comp_aestronglyMeasurable (hc.aestronglyMeasurable (μ := d.μ.restrict d.D))
  simpa only [hΨ] using this

theorem lem_gap (hGap : SGap) (hC : IsTotallyComplex L) (π : 𝓞 L) (hπ : Prime π)
    (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (h3N : 3 ≤ N) (d : Dom L N) (f : Gp L N → ℝ) (hf : Lz d f)
    (r : ℕ) : Lz d ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) ∧
      ∫ x in d.D, ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) (ofS L N x) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ := by
  induction r with
  | zero => exact ⟨hf, by simp⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := hGap L hC π hπ hπ25 N h3N d _ ih.1
    rw [Function.iterate_succ_apply']
    refine ⟨h1, h2.trans ((mul_le_mul_of_nonneg_left ih.2 (by norm_num)).trans (le_of_eq ?_))⟩
    ring

end Analytic

theorem lem_bound (hGap : SGap) (hLoc : SLoc) (L : Type) [Field L] [NumberField L] (hC : IsTotallyComplex L)
    (π : 𝓞 L) (hπ : Prime π) (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (N k : ℕ) (h3N : 3 ≤ N)
    (d : Dom L N) (ω₀ : Form (HS L N) (k + 1)) (hω₀G : Good ω₀) (hω₀γ : ∀ γ, FInv ω₀ (emb L N γ))
    (hω₀s : ∀ s, FInv ω₀ (scal L N s)) (hLz0 : ∀ u : Fin (k + 1) → HS L N, Lz d (fun x => fr ω₀ x u))
    (z : Chn (Gm L N) (k + 1)) (hz : IsCyc z) :
    ∃ C : ℝ, ∀ r : ℕ, |ev (toK L N) ((hecke (toK L N) (MonoidHom.id (GK L N)) (qel L N π hπ.ne_zero))^[r]
      (fun y => intP ω₀ fun j => toP L N (y j) • one L N)) 1 z| ≤ C * (3 / 5 : ℝ) ^ r := by
  obtain ⟨K, hK0, hK⟩ := lem_nrm (L := L) (N := N) k
  obtain ⟨Cz, hCz⟩ := hLoc L N k (by omega) d z hz
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := ⟨_, rfl⟩
  refine ⟨|Cz| * √(K * S0), fun r => ?_⟩
  rw [ev_toK _ _ (hecke_iter (qel L N π hπ.ne_zero) hω₀G.1 r) z]
  obtain ⟨ωr, hωr⟩ : ∃ ωr, ωr = (Hk (qel L N π hπ.ne_zero))^[r] ω₀ := ⟨_, rfl⟩
  rw [← hωr]
  obtain ⟨hrG, hrγ, hrs⟩ := Hk_iter_props (qel L N π hπ.ne_zero) hω₀G hω₀γ hω₀s r
  rw [← hωr] at hrG hrγ hrs
  have hLzr : ∀ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      Lz d (fun x => fr ωr x fun i => Module.finBasis ℝ (HS L N) (v i)) ∧
      ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
    fun v => by
      have := lem_gap hGap hC π hπ hπ25 h3N d _ (hLz0 (fun i => Module.finBasis ℝ (HS L N) (v i))) r
      rw [← comp_Hk_iter, ← hωr] at this
      exact this
  have hsumint : Integrable (fun x => K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2) (d.μ.restrict d.D) :=
    (integrable_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1).const_mul _
  have hint_r : IntegrableOn (fun x => ‖fr ωr (ofS L N x)‖ ^ 2) d.D d.μ :=
    Integrable.mono' hsumint ((lem_meas d hrG.1).norm.pow 2) (Filter.Eventually.of_forall fun x => by
      show ‖‖fr ωr (ofS L N x)‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hK _)
  have hIr : ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ ≤ ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by
    calc ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ
        ≤ ∫ x in d.D, K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          integral_mono hint_r hsumint fun x => hK _
      _ = K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := by
          rw [integral_const_mul, integral_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1]
      _ ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)), ((3 / 5 : ℝ) ^ 2) ^ r *
            ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => (hLzr v).2) hK0
      _ = ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by rw [hS0, ← Finset.mul_sum]; ring
  have hsq : √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) = (3 / 5 : ℝ) ^ r * √(K * S0) := by
    rw [← pow_mul, mul_comm 2 r, pow_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc |ev (emb L N) (intP ωr) (one L N) z|
      ≤ Cz * √(∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ) := hCz _ hrG hrγ hrs hint_r
    _ ≤ |Cz| * √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) :=
        mul_le_mul (le_abs_self _) (Real.sqrt_le_sqrt hIr) (Real.sqrt_nonneg _) (abs_nonneg _)
    _ = |Cz| * √(K * S0) * (3 / 5 : ℝ) ^ r := by rw [hsq]; ring

end PositivityTheory.KB.JoinReconstruction

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemLz

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_Lz {L : Type} [Field L] [NumberField L] {N k : ℕ} (d : Dom L N) {ω' ωb : Form (HS L N) (k + 1)}
    (hω'c : ContinuousOn ω' (Pos L N)) (hωbc : ContinuousOn ωb (Pos L N))
    (hγ : ∀ γ, FInv (ω' - ωb) (emb L N γ)) (hs : ∀ s, FInv (ω' - ωb) (scal L N s))
    (hωbfr : ∀ x, fr ωb x = (d.μ.real d.D)⁻¹ • ∫ y in d.D, fr ω' (ofS L N y) ∂d.μ)
    (hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ)
    (hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ) (u : Fin (k + 1) → HS L N) :
    Lz d (fun x => fr (ω' - ωb) x u) := by
  let E : (HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => HS L N) ℝ u).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hE : ∀ F, E F = F u := fun F => rfl
  have hf : IntegrableOn (fun y => fr ω' (ofS L N y) u) d.D d.μ := E.integrable_comp hint'
  set c : ℝ := (d.μ.real d.D)⁻¹ * ∫ y in d.D, fr ω' (ofS L N y) u ∂d.μ with hcdef
  have hc : ∀ x, fr ωb x u = c := by
    intro x
    rw [hωbfr x, ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← hE,
      ← ContinuousLinearMap.integral_comp_comm E hint']
    rfl
  have hfun : ∀ x, fr (ω' - ωb) x u = fr ω' x u - c := by
    intro x
    rw [fr_sub, ContinuousAlternatingMap.sub_apply, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fr_comp_cont (hω'c.sub hωbc) u
  · intro γ x
    simp only [fr_inv (hγ γ) x]
  · intro s x
    simp only [fr_inv (hs s) x]
  · simp only [hfun]
    have hg : IntegrableOn (fun x => 2 * ‖E‖ ^ 2 * ‖fr ω' (ofS L N x)‖ ^ 2 + 2 * c ^ 2) d.D d.μ :=
      (hsq'.const_mul (2 * ‖E‖ ^ 2)).add (integrableOn_const d.fin.ne)
    refine Integrable.mono' hg ?_ ?_
    · exact ((continuous_id.sub continuous_const).pow 2).comp_aestronglyMeasurable
        (E.integrable_comp hint').aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : |E (fr ω' (ofS L N x))| ≤ ‖E‖ * ‖fr ω' (ofS L N x)‖ := by
        rw [← Real.norm_eq_abs]
        exact E.le_opNorm _
      have h2 : (fr ω' (ofS L N x) u) ^ 2 ≤ (‖E‖ * ‖fr ω' (ofS L N x)‖) ^ 2 := by
        rw [← hE, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (fr ω' (ofS L N x) u + c)]
  · simp only [hfun]
    rw [integral_sub hf (integrableOn_const d.fin.ne), setIntegral_const, smul_eq_mul]
    rcases eq_or_ne (d.μ.real d.D) 0 with h0 | h0
    · have hz : d.μ d.D = 0 := (measureReal_eq_zero_iff d.fin.ne).mp h0
      rw [setIntegral_measure_zero _ hz, h0, zero_mul, sub_zero]
    · rw [hcdef, mul_inv_cancel_left₀ h0, sub_self]

end PositivityTheory.KB.JoinReconstruction

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemForm

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_form (hHt : SHt) (hPU : SPU) (hWhit : SWhit) (hCen : SCen) (L : Type) [Field L] [NumberField L]
    (hC : IsTotallyComplex L) (k a N : ℕ) (h1N : 1 ≤ N) (hPUa : Nonempty (PU L N fun x => ht x ^ a))
    (c : (Fin (k + 2) → Gm L N) → ℝ) (hcI : Inv (MonoidHom.id (Gm L N)) c) (hcd : dC c = 0) :
    ∃ ω' : Form (HS L N) (k + 1), Good ω' ∧ (∀ γ, FInv ω' (emb L N γ)) ∧ (∀ s, FInv ω' (scal L N s)) ∧
      (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
        ev (emb L N) (intP ω') (one L N) z = ev (MonoidHom.id (Gm L N)) c 1 z) ∧
      ∃ K, ∀ x, ‖fr ω' x‖ ≤ K * ht x ^ (a * (k + 1)) := by
  obtain ⟨P⟩ := hPUa
  obtain ⟨_, hHtinv, ⟨c0, hc0, hc0le⟩, hHtK⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  obtain ⟨ω, hωG, hωγ, hωs, hωz, C1, hC1⟩ := hWhit L N k (fun x => ht x ^ a) P
    (fun γ x => by simp only [hHtinv]) (fun x => pow_nonneg (hht0 x) _) c hcI hcd
  obtain ⟨p, hp⟩ : ∃ p, p = a * (k + 1) := ⟨_, rfl⟩
  have hfrB : ∀ x, ‖fr ω x‖ ≤ |C1| * ht x ^ p := fun x => by
    calc ‖fr ω x‖ ≤ C1 * (ht x ^ a) ^ (k + 1) := hC1 x
      _ ≤ |C1| * (ht x ^ a) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (pow_nonneg (hht0 x) _) _)
      _ = |C1| * ht x ^ p := by rw [hp, ← pow_mul]
  have hB : ∀ K : Set (Gp L N), IsCompact K →
      ∃ C, ∀ g ∈ K, ∀ x, |C1| * ht (x * g) ^ p ≤ C * (|C1| * ht x ^ p) := by
    intro K hK
    obtain ⟨C, hC⟩ := hHtK K hK
    refine ⟨|C| ^ p, fun g hg x => ?_⟩
    have h1 : ht (x * g) ≤ |C| * ht x :=
      (hC g hg x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hht0 x))
    calc |C1| * ht (x * g) ^ p ≤ |C1| * (|C| * ht x) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hht0 _) h1 p) (abs_nonneg _)
      _ = |C| ^ p * (|C1| * ht x ^ p) := by rw [mul_pow]; ring
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, C2, hC2⟩ :=
    hCen L N k ω hωG hωγ hωs (fun x => |C1| * ht x ^ p) hB hfrB
  refine ⟨ω', hω'G, hω'γ, hω's, fun z hz => (hω'z z hz).trans (hωz z hz), |C2| * |C1|, fun x => ?_⟩
  rw [← hp]
  calc ‖fr ω' x‖ ≤ C2 * (|C1| * ht x ^ p) := hC2 x
    _ ≤ |C2| * (|C1| * ht x ^ p) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (abs_nonneg _) (pow_nonneg (hht0 x) _))
    _ = |C2| * |C1| * ht x ^ p := by ring

theorem key (hPrime : SPrime) (hHecke : SHecke) (hHt : SHt) (hPU : SPU) (hMom : SMom) (hWhit : SWhit)
    (hCen : SCen) (hGap : SGap) (hLoc : SLoc) (hMean : SMean) (hInv : SInv) : SSurj := by
  intro L _ _ hC k hkr n₀
  obtain ⟨π, hπ, hπ25⟩ := hPrime L
  obtain ⟨a, hPUa⟩ := hPU L hC
  obtain ⟨N₀, hN₀⟩ := hHecke L hC k hkr π hπ
  obtain ⟨N₁, hN₁⟩ := hMom L hC (2 * (a * (k + 1)))
  obtain ⟨N, hN⟩ : ∃ N, N = max (max N₀ N₁) (max n₀ 3) := ⟨_, rfl⟩
  have hN0 : N₀ ≤ N := by rw [hN]; exact (le_max_left N₀ N₁).trans (le_max_left _ _)
  have hN1 : N₁ ≤ N := by rw [hN]; exact (le_max_right N₀ N₁).trans (le_max_left _ _)
  have hn₀ : n₀ ≤ N := by rw [hN]; exact (le_max_left n₀ 3).trans (le_max_right _ _)
  have h3N : 3 ≤ N := by rw [hN]; exact (le_max_right n₀ 3).trans (le_max_right _ _)
  have h1N : 1 ≤ N := by omega
  refine ⟨N, hn₀, fun c hcI hcd => ?_⟩
  obtain ⟨d, hd⟩ := hN₁ N hN1
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, K, hK⟩ :=
    lem_form hHt hPU hWhit hCen L hC k a N h1N (hPUa N h1N) c hcI hcd
  obtain ⟨_, _, ⟨c0, hc0, hc0le⟩, _⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.2 d.fin.ne
  have hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ := by
    refine Integrable.mono' (hd.const_mul (K ^ 2)) ((lem_meas d hω'G.1).norm.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖‖fr ω' (ofS L N x)‖ ^ 2‖ ≤ K ^ 2 * ht (ofS L N x) ^ (2 * (a * (k + 1)))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm 2 (a * (k + 1)), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK _) 2
  have hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ := by
    refine Integrable.mono' (hsq'.add (integrable_const (1 : ℝ))) (lem_meas d hω'G.1)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖fr ω' (ofS L N x)‖ ≤ ‖fr ω' (ofS L N x)‖ ^ 2 + 1
    nlinarith [sq_nonneg (‖fr ω' (ofS L N x)‖ - 1)]
  obtain ⟨ωb, hωbI, hωbfr⟩ := hMean L N (k + 1) h1N d ω' hω'G.1 hω'γ hω's hint'
  have hωbG : Good ωb := (hInv L N k ωb hωbI).1
  have hγ0 : ∀ γ, FInv (ω' - ωb) (emb L N γ) := fun γ => finv_sub (hω'γ γ) (hωbI _)
  have hs0 : ∀ s, FInv (ω' - ωb) (scal L N s) := fun s => finv_sub (hω's s) (hωbI _)
  have hLz0 := lem_Lz d hω'G.1 hωbG.1 hγ0 hs0 hωbfr hint' hsq'
  have e2 : intP (ω' - ωb) = fun y => intP ω' y - intP ωb y := funext (intP_sub hω'G.1 hωbG.1)
  have hG0 : Good (ω' - ωb) := by
    refine ⟨hω'G.1.sub hωbG.1, ?_⟩
    rw [e2, dC_sub, hω'G.2, hωbG.2]
    funext y
    simp
  have hFI : Inv (toK L N) (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) :=
    fun γ y => by
      show (intP (ω' - ωb) fun j => toP L N (toK L N γ • y j) • one L N) =
        intP (ω' - ωb) fun j => toP L N (y j) • one L N
      simp only [smul_eq_mul, map_mul, mul_smul]
      exact intP_inv (hγ0 γ) _
  have hFd : dC (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) = 0 := by
    funext y
    have h4 := congrFun hG0.2 (fun j => toP L N (y j) • one L N)
    simp only [dC, Pi.zero_apply] at h4 ⊢
    exact h4
  have hF0 := hN₀ N hN0 _ hFI hFd fun z hz =>
    lem_bound hGap hLoc L hC π hπ hπ25 N k h3N d (ω' - ωb) hG0 hγ0 hs0 hLz0 z hz
  refine ⟨ωb, hωbI, fun z hz => ?_⟩
  have h5 := hF0 z hz
  rw [ev_toK _ (intP (ω' - ωb)) (fun y => rfl) z, e2, ev_sub] at h5
  rw [← hω'z z hz]
  linarith

end PositivityTheory.KB.JoinReconstruction

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SurjectivityCase.SSurjOf

section

@[expose] public section

namespace PositivityTheory.KB

theorem sSurj_of : SPrime → SHecke → SHt → SPU → SMom → SWhit → SCen → SGap → SLoc → SMean → SInv → SSurj :=
  JoinReconstruction.key

end PositivityTheory.KB
end
end
