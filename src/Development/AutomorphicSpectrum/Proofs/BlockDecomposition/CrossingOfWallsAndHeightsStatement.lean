module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoarseLipschitzExponentialEstimateStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTubeStatement
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSeriesSummableShifted

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEis


open PositivityTheory.RgEis in
theorem cross_stage_pos : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  open PositivityTheory.RgEis in
  intro hS G _ Γ Q P ξ lam t hPQ hξ hlam hc g
  have key := (hS G ℝ P (Γ ⊓ Q) Γ (fun x => Real.exp (lam x + t * ξ x)) inf_le_left
    (fun γ h1 h2 => ⟨h1, hPQ h2⟩)
    (fun γ h1 h2 x => by
      show Real.exp (lam (γ * x) + t * ξ (γ * x)) = Real.exp (lam x + t * ξ x)
      rw [hlam γ h1 h2 x, hξ γ h1 (hPQ h2) x]) g
    (by
      have h := hc g
      refine h.congr (fun q => ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])).2.1
  refine key.congr (fun r => ?_)
  rw [pos, ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hξ _ hq.1 hq.2, ← Real.exp_add, add_comm]

end GlobalTheory.CompanionTheory.RgEis
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSeriesSummableShiftedStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.coset_series_summable_shifted : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | exact GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | (intros; apply GlobalTheory.CompanionTheory.RgEis.cross_stage_pos <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvarianceCosetSum

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross


open PositivityTheory.RgEis in
theorem stage_eis : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  intro hSt G _ W _ _ _ Γ K Q P c ρ ξ lam Λ s w Ms hPQ hξ hΛ hsec hMs hconv hre g
  set f : G → W := fun x => Complex.exp (Λ x + s * ξ x) • sec K P c ρ x w with hf
  have hfinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro γ hγ hP x
    simp only [hf]
    rw [hΛ γ hγ hP x, hξ γ hγ (hPQ hP) x, hsec γ hγ hP x]
  have hnorm : ∀ x, ‖f x‖ ≤ Ms * Real.exp (lam x) := by
    intro x
    simp only [hf]
    rw [norm_smul, Complex.norm_exp, hre x, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right (hMs x) (Real.exp_pos _).le
  have hsum : Summable fun q : Cos P Γ => ‖f (rep q * g)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hnorm _) ((hconv g).mul_left Ms)
  obtain ⟨-, -, hstage⟩ := hSt G W P (Γ ⊓ Q) Γ f inf_le_left (fun γ hγ hP => ⟨hγ, hPQ hP⟩) hfinv g hsum
  have hR : eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w = ∑' q : Cos P Γ, f (rep q * g) := rfl
  rw [hR, hstage]
  unfold eis
  refine tsum_congr fun r => ?_
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  simp only [hf]
  rw [hξ _ (Subgroup.mem_inf.mp hq).1 (Subgroup.mem_inf.mp hq).2, Complex.exp_add, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisCross
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvarianceCosetSumStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.section_invariance_coset_sum : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.stage_eis | exact GlobalTheory.CompanionTheory.RgEisCross.stage_eis | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.stage_eis <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights

section

@[expose] public section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem sec_inv {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  intro γ hγ hγP x
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have h1 := law (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := law p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, hP.ch.mul γ hγP p hp, hP.ch.rat γ hγ hγP, one_mul]

theorem cross (hSec : SecLaw) (hHt : HtLip) (hSt : PiLocalization₂) (hWL : WallLaw) : Cross := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ Q P P' c η η' β ξ L R D Op H Ω hPQ hP'Q hP hP' hη hη' hβ hξ hW hΩ hx
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have parRes : ∀ (P : Subgroup G), IsPar Γ K P c → IsPar (Γ ⊓ Q) K P c := fun _ h =>
    ⟨h.closed, h.iwa, ⟨h.ch.mul, h.ch.norm, fun γ hγ hp => h.ch.rat γ hγ.1 hp, h.ch.cont⟩⟩
  have htRes : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → IsHt (Γ ⊓ Q) K P f := fun _ _ h =>
    ⟨h.left, h.right, fun γ hγ hp => h.rat γ hγ.1 hp, h.cont⟩
  obtain ⟨-, -, hbound⟩ := hWL G W K ρ hK hρ (Γ ⊓ Q) P P' c η η' β L R D Op H (parRes P hP) (parRes P' hP')
    (htRes P η hη) (htRes P' η' hη') (htRes P' β hβ) hW
  have hξinv : ∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x := by
    intro γ h1 h2 x
    rw [hξ.left γ h2, hξ.rat γ h1 h2, zero_add]
  have htinv : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro P f hf γ h1 h2 x
    rw [hf.left γ h2, hf.rat γ h1 h2, zero_add]
  have iwaQ : Iwa Q K := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hP.iwa g
    exact ⟨p, hPQ hp, k, hk, e⟩
  have mξ := hHt G Γ K Q ξ hK iwaQ hξ
  have mη := hHt G Γ K P η hK hP.iwa hη
  have mη' := hHt G Γ K P' η' hK hP'.iwa hη'
  have mβ := hHt G Γ K P' β hK hP'.iwa hβ
  let t : Cos (Γ ⊓ Q) Γ → ℂ × ℂ → G → (L →L[ℂ] W) := fun r l g =>
    Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
  have hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g := by
    intro r g p v
    have h1 : Differentiable ℂ fun τ : ℂ => H (p + τ • v).1 (rep r * g) :=
      (hW.hol (rep r * g)).comp (by fun_prop)
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).2 * ξ (rep r * g)) := by fun_prop
    exact h2.smul h1
  have hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × G => t r y.1 y.2 := by
    intro r
    have h0 : Continuous fun y : (ℂ × ℂ) × G => rep r * y.2 := by fun_prop
    have h1 : Continuous fun y : (ℂ × ℂ) × G => H y.1.1 (rep r * y.2) :=
      hW.cont.comp (continuous_fst.fst.prodMk h0)
    have h2 : Continuous fun y : (ℂ × ℂ) × G => ξ (rep r * y.2) := hξ.cont.comp h0
    have h3 : Continuous fun y : (ℂ × ℂ) × G => Complex.exp (y.1.2 * ξ (rep r * y.2)) :=
      Complex.continuous_exp.comp ((continuous_fst.snd).mul (Complex.continuous_ofReal.comp h2))
    exact h3.smul h1
  have hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : Cos (Γ ⊓ Q) Γ → ℝ, Summable u ∧
      ∀ l ∈ tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r := by
    intro x hxΩ g
    obtain ⟨a, b, ε, hε, hRa, hbR, hbx, hxa, hconv⟩ := hx x hxΩ
    obtain ⟨M, hM⟩ := hbound a b hRa hbR
    have inv₁ : ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => a * η x) (γ * x) = (fun x => a * η x) x := by
      intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    have inv₂ : ∀ γ ∈ Γ, γ ∈ P' → ∀ x, (fun x => β x - b * η' x) (γ * x) = (fun x => β x - b * η' x) x := by
      intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    have m₁ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |a * η (g * u) - a * η g| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη C hC
      refine ⟨|a| * A, fun g u hu => ?_⟩
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg a)
    have m₂ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C,
        |(β (g * u) - b * η' (g * u)) - (β g - b * η' g)| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη' C hC
      obtain ⟨B, hB⟩ := mβ C hC
      refine ⟨B + |b| * A, fun g u hu => ?_⟩
      have e : (β (g * u) - b * η' (g * u)) - (β g - b * η' g) =
          (β (g * u) - β g) - b * (η' (g * u) - η' g) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hB g u hu) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg b)
    have hl : |x.2 - ε - x.2| ≤ ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]
    have hr : |x.2 + ε - x.2| ≤ ε := by rw [add_sub_cancel_left, abs_of_pos hε]
    obtain ⟨U, hU, u, hu, hb⟩ := GlobalTheory.T.coarse_lipschitz_exponential_estimate G (L →L[ℂ] W) Γ (Γ ⊓ Q) P P' ξ (fun x => a * η x) (fun x => β x - b * η' x) H a b
      (x.2 - ε) (x.2 + ε) M mξ m₁ m₂ (hW.convR a hRa) (hW.convL b hbR) hM
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hl).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hr).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hl).2)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hr).2) g
    refine ⟨Set.Icc b a ×ˢ Set.Icc (x.2 - ε) (x.2 + ε),
      prod_mem_nhds (Icc_mem_nhds hbx hxa) (Icc_mem_nhds (by linarith) (by linarith)), U, hU, u, hu, ?_⟩
    intro l hl g' hg' r
    obtain ⟨h1, h2⟩ := hl
    exact hb l h1.1 h1.2 h2.1 h2.2 g' hg' r
  obtain ⟨hTG, hsum⟩ := GlobalTheory.T.holomorphic_series_uniform_tube _ _ _ t Ω hhol hcont hdom
  have key : ∀ l ∈ tube Ω, ∀ g (w : L), outer Γ (Γ ⊓ Q) ξ H l g w =
      ∑' r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by
    intro l hl g w
    have hs : Summable fun r => t r l g := (hsum l hl g).of_norm
    exact (ContinuousLinearMap.apply ℂ W w).map_tsum hs
  obtain ⟨law, -, Ms, hMs⟩ := hSec G W K ρ hK hρ Γ P c hP
  obtain ⟨law', -, Ms', hMs'⟩ := hSec G W K ρ hK hρ Γ P' c hP'
  refine ⟨hTG, hsum, ?_, ?_⟩
  · intro l hl hRl hconv g w
    have hw : (w : W) ∈ secSp K P c ρ := hW.le w.2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        D l.1 • (Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P c ρ (fun x => l.1 * η x) (rep r * g) w) := by
      intro r
      rw [hW.eqR l.1 hRl, smul_comm]
    simp_rw [e]
    rw [tsum_const_smul'']
    congr 1
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P c ρ ξ (fun x => l.1.re * η x + l.2.re * ξ x) (fun x => l.1 * η x) l.2 w
      (Ms * ‖(w : W)‖) hPQ hξinv ?_ (sec_inv hP (law w hw)) (fun x => hMs x w) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    · intro x
      simp
  · intro l hl hRl hconv g w
    have hw : ((Op l.1 w : secSp K P' c ρ) : W) ∈ secSp K P' c ρ := (Op l.1 w).2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P' c ρ (fun x => β x - l.1 * η' x) (rep r * g) (Op l.1 w) := by
      intro r
      rw [hW.eqL l.1 hRl]
    simp_rw [e]
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P' c ρ ξ (fun x => β x - l.1.re * η' x + l.2.re * ξ x)
      (fun x => (β x : ℂ) - l.1 * η' x) l.2 _ (Ms' * ‖((Op l.1 w : secSp K P' c ρ) : W)‖) hP'Q hξinv ?_
      (sec_inv hP' (law' _ hw)) (fun x => hMs' x _) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    · intro x
      simp

end GlobalTheory.CompanionTheory.RgEisCross
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeightsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.crossing_of_walls_and_heights : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.HtLip → PositivityTheory.RgEis.PiLocalization₂ → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Cross := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.cross | exact GlobalTheory.CompanionTheory.RgEisCross.cross | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.cross <;> assumption)
end
end
