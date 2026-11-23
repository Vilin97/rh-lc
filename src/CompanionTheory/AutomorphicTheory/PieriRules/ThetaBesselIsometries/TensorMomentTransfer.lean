module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Mathlib.MeasureTheory.Function.L2Space
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUnique
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselSideBoundStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroupStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselSideBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransferStatement
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselCompare

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselOrth

section L2

variable {X E : Type} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_toLp {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem integrable_inner {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) ν := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem norm_toLp_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {f : X → E} (hf : MemLp f 2 ν)
    {a : H} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) : ‖hf.toLp f‖ = ‖a‖ := by
  rw [← inner_toLp hf hf] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h]

theorem norm_integral_inner_le {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    {a : H} {b : H'} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) (h' : ∫ x, ⟪g x, g x⟫_ℂ ∂ν = ⟪b, b⟫_ℂ) :
    ‖∫ x, ⟪f x, g x⟫_ℂ ∂ν‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← inner_toLp hf hg, ← norm_toLp_eq hf h, ← norm_toLp_eq hg h']
  exact norm_inner_le_norm _ _

end L2

end GlobalTheory.BesselOrth

namespace GlobalTheory

open BesselOrth Formalism.FourierDecayAlt.P

theorem bessel_orth_of_param_ne : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDG ε mu → R'.IsDG ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  intro hH k r ε mu mu' R R' Wp _ _ _ _ z π u μW μN μG νq Bm Bm' hR hR' hne hS hB hB'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : PoulsenG := hH.2.2.2.2.2.1
  obtain ⟨hL, hI⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu R Wp z π u μW μN μG νq Bm hR hS hB
  obtain ⟨hL', hI'⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu' R' Wp z π u μW μN μG νq Bm' hR' hS hB'
  have hq := GlobalTheory.T.quotientMeasure_integral_rmul_besselGroup k r Wp z π u μW μN μG νq
  obtain ⟨⟨ha, hs, he, hc⟩, -⟩ := hB
  obtain ⟨⟨ha', hs', he', hc'⟩, -⟩ := hB'
  have hco := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp Bm ha hs hc
  have hco' := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu' R' hR' Wp Bm' ha' hs' hc'
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
    obtain ⟨-, -, -, -, hW, hN, hG, hQ⟩ := hS
    exact DDSmoothness.ae_UH_of_quot hG.2.2.1 (DDSmoothness.muSof_facts hW hN).1 (DDSmoothness.muSof_facts hW hN).2 hQ
  have ht : ∀ w ∈ R.sm, ∀ g ∈ GG k r, R.σ g w ∈ R.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR.2 hw hg
  have ht' : ∀ w ∈ R'.sm, ∀ g ∈ GG k r, R'.σ g w ∈ R'.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR'.2 hw hg
  have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R.σ (a * b) v = R.σ a (R.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR.2 ha hb]; rfl
  have hm' : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R'.σ (a * b) v = R'.σ a (R'.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR'.2 ha hb]; rfl
  have hform : IsInvForm R R' (fun w y =>
      ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, 1, [[]], [[]], by simp, ?_⟩
    · intro w hw w' hw' y hy
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y hy) (hL w' hw'))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha _ (ht w hw _ hx) _ (ht w' hw' _ hx), inner_add_right]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs a _ (ht w hw _ hx), inner_smul_right]
    · intro w hw y hy y' hy'
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y' hy') (hL w hw))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha' _ (ht' y hy _ hx) _ (ht' y' hy' _ hx), inner_add_left]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs' a _ (ht' y hy _ hx), inner_smul_left]
      rfl
    · intro g hg w hw y hy
      beta_reduce
      have key := hq (fun x => ⟪Bm' (R'.σ x y), Bm (R.σ x w)⟫_ℂ) hS
        (ContinuousOn.inner (𝕜 := ℂ) (hco' y hy).1 (hco w hw).1) ?_ (integrable_inner (hL' y hy) (hL w hw)) g hg
      · rw [← key]
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hm _ hx _ hg, hm' _ hx _ hg]
      · rintro s ⟨h, hh, m, hmN, rfl⟩ x hx
        obtain ⟨-, hT, ⟨u₀, hπ⟩, -⟩ := hS
        have hsG : h * m ∈ GG k r := DDSmoothness.uh_mul hh.1 hmN.1
        have hiso : ∀ a b, ⟪π h a, π h b⟫_ℂ = ⟪a, b⟫_ℂ :=
          (LinearMap.norm_map_iff_inner_map_map ((π h : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1
            (MatrixMultiplicationContinuity.piW_unitary hT hπ h hh)
        have hψ := MatrixMultiplicationContinuity.psi_norm z Formalism.QuantumDeterminants.cStd m
        beta_reduce
        rw [hm _ hsG _ hx, hm' _ hsG _ hx, he h hh m hmN _ (ht w hw _ hx), he' h hh m hmN _ (ht' y hy _ hx),
          inner_smul_left, inner_smul_right, hiso, ← mul_assoc, Complex.conj_mul', hψ]
        simp
    · intro w hw y hy
      have := norm_integral_inner_le (hL' y hy) (hL w hw) (hI' y hy y hy) (hI w hw w hw)
      simpa [PI.UpqRep.dsigW, mul_comm] using this
  rcases (hP k r ε mu mu' R R' hR hR').2 _ hform with h | ⟨U, hU⟩
  · exact h
  · exact absurd (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε mu mu' R R' hR hR' U hU) hne

end GlobalTheory

end
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsometricBesselCompareStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.isometric_bessel_compare : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDG ε mu → R'.IsDG ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  first | exact @GlobalTheory.bessel_orth_of_param_ne | exact GlobalTheory.bessel_orth_of_param_ne | (intros; apply GlobalTheory.bessel_orth_of_param_ne <;> assumption)
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentTransfer

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPairing

theorem integrable_inner_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem add_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    v + w ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv hw ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  obtain ⟨U2, F2, hU2, h2, hF2, e2⟩ := hw g₀ h₀
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨h1, h2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  show (R.σ g) (v + w) = F1 g + F2 g
  rw [map_add (f := _)]
  exact congrArg₂ (· + ·) (e1 g hg.1 hgH) (e2 g hg.2 hgH)

private theorem smul_mem_sm' {k r : ℕ} (R : BranchingSupport.Rep k r) (c : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    c • v ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv ⊢
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ h₀
  obtain ⟨U1, F1, hU1, h1, hF1, e1⟩ := hv g₀ h₀
  refine ⟨U1, fun x => c • F1 x, hU1, h1, hF1.const_smul c, fun g hg hgH => ?_⟩
  show (R.σ g) (c • v) = c • F1 g
  rw [map_smul]
  exact congrArg (c • ·) (e1 g hg hgH)

private theorem zero_mem_sm {k r : ℕ} (R : BranchingSupport.Rep k r) : (0 : R.H) ∈ R.sm := by
  simp only [BranchingSupport.Rep.sm, PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec]
  letI : NormedAddCommGroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.normedSpace
  intro g₀ _
  refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  show (R.σ g) 0 = 0
  exact map_zero _

theorem pairing : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  intro hyp k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hT hS
    hB hOr hev I hIso y hy a w hw
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hpr : ∀ J c, BranchingSupport.SmMap R (RI J) (pr J c) := by
    cases hT
    assumption
  have hv : ∀ J, (∑ c, pr J c (BranchingSupport.tm R a w c)) ∈ (RI J).sm := by
    intro J
    refine Finset.sum_induction _ (· ∈ (RI J).sm) (fun p q hp hq => add_mem_sm (RI J) hp hq)
      (zero_mem_sm (RI J)) ?_
    intro c _
    obtain ⟨hmem, -, -, -⟩ := hpr J c
    exact hmem _ (smul_mem_sm' R (a c) hw)
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS).1
  have hpt : ∀ᵐ x ∂νq, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ =
      ∑ J, β J * ⟪BI I ((RI I).σ (Matrix.of x) y), BI J ((RI J).σ (Matrix.of x) (∑ c, pr J c (BranchingSupport.tm R a w c)))⟫_ℂ := by
    filter_upwards [hae] with x hx
    rw [Gp91.GlobalTheory.T.tensor_bessel_transfer hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp om Bm BI β hR hRI hT hB.1 hB.2.1 hev a w hw
      (Matrix.of x) hx, inner_sum]
    simp only [inner_smul_right]
  refine (MeasureTheory.integral_congr_ae hpt).trans ?_
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_eq_single I]
    · rw [MeasureTheory.integral_const_mul,
        (Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).2 _ (hv I) y hy]
    · intro J _ hJI
      rw [MeasureTheory.integral_const_mul]
      rcases hOr J with hJ | hJ
      · rw [Gp91.GlobalTheory.T.isometric_bessel_compare hyp k r ε (muI J) (muI I) (RI J) (RI I) Wp z π u μW μN μG νq (BI J) (BI I)
          (hRI J) (hRI I) (fun h => hJI (hinj h)) hS hJ hIso _ (hv J) y hy, mul_zero]
      · rw [hJ, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ I) h
  · intro J _
    rcases hOr J with hJ | hJ
    · exact (integrable_inner_of_memLp
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hIso).1 y hy)
        ((Gp91.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI J) (RI J) Wp z π u μW μN μG νq (BI J) (hRI J) hS hJ).1 _
          (hv J))).const_mul (β J)
    · simp only [hJ, zero_mul]
      exact MeasureTheory.integrable_zero _ _ _

end GlobalTheory.BesselPairing
end Gp91
end
end
