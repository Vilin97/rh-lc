module

public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
public import Formalism.HermitianCurvature.HerGenC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBoundStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinearStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompactStatement
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Complex.Basic
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TvApproxTendstoL2CutoffStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolarisationOnSubspace

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by
  intro V _ _ S B T hS hB hT hd x y hx hy
  have key : ∀ a : ℂ, a * B y x + (starRingEnd ℂ) a * B x y = a * T y x + (starRingEnd ℂ) a * T x y := by
    intro a
    have h := hd _ (hS a x y hx hy)
    rw [hB a x y hx hy, hT a x y hx hy, hd x hx, hd y hy] at h
    linear_combination h
  have h1 := key 1
  have h2 := key Complex.I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2
    - ((B y x - T y x - B x y + T x y) / 2) * Complex.I_mul_I

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVecPol

theorem integrable_inner_of_memLp {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun c => inner ℂ (u c) (v c)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with c h1 h2
  rw [h1, h2]

theorem integral_inner_expand {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (a : ℂ) :
    ∫ c, inner ℂ (u c + a • v c) (u c + a • v c) ∂μ =
      ∫ c, inner ℂ (u c) (u c) ∂μ + a * ∫ c, inner ℂ (u c) (v c) ∂μ +
        (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (u c) ∂μ +
        a * (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (v c) ∂μ := by
  have h1 := integrable_inner_of_memLp hu hu
  have h2 := (integrable_inner_of_memLp hu hv).const_mul a
  have h3 := (integrable_inner_of_memLp hv hu).const_mul ((starRingEnd ℂ) a)
  have h4 := (integrable_inner_of_memLp hv hv).const_mul (a * (starRingEnd ℂ) a)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have h12 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c)) μ := h1.add h2
  have h123 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c) +
      (starRingEnd ℂ) a * inner ℂ (v c) (u c)) μ := h12.add h3
  rw [← integral_add h12 h3, ← integral_add h123 h4]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

theorem beta_eq_integral_inner_tv : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H H' w hD hH hH' hw
  have hS : ∀ (a : ℂ) (x y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base x → KB.CptCoef p.T.base y →
      KB.CptCoef p.T.base (x + a • y) := fun a x y hx hy => Formalism.FourierDecayAlt.P.PBL.cpt_add hx (Formalism.FourierDecayAlt.P.PBL.cpt_smul a hy)
  have hcc : ∀ x : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base x → ∀ (A : ℝ) (m : ℕ), B.InCC A m x := by
    intro x hx
    obtain ⟨ε, -, h⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hx
    exact h.2.1
  refine GlobalTheory.polarisation_on_subspace (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (KB.CptCoef p.T.base)
    (fun x y => B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) x w) y)
    (fun x y => ∫ c, inner ℂ (tv p y w c) (tv p x w c)) hS ?_ ?_ ?_ H H' hH hH'
  · intro a x y hx hy
    have hs := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w (B.AB P.k P.r) le_rfl a
    have hz := hS a x y hx hy
    have e1 := (hs x y (x + a • y) x hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc _ hz _ _) (hcc x hx _ _)).1
    have e2 := (hs x y x y hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    have e3 := (hs y y x y hy.1 hy.1 (hcc y hy _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    beta_reduce
    rw [e1, e2, e3]
    ring
  · intro a x y hx hy
    have hx2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).1
    have hy2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb y w hD hy hw).1
    have e : ∀ c, tv p (x + a • y) w c = tv p x w c + a • tv p y w c := fun c =>
      GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb a x y w c hD hw hx hy
    beta_reduce
    simp only [e]
    exact integral_inner_expand hx2 hy2 a
  · intro x hx
    beta_reduce
    rw [(GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    simp

end GlobalTheory.TopVecPol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectorsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  first | exact @GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | exact GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | (intros; apply GlobalTheory.TopVecPol.beta_eq_integral_inner_tv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoIntegralInnerOfTendstoELpNormTwo

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectors

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_word_cutF_eq_integral_inner_tv :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  intro hA Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tv_approx_tendsto_L2_cutoff hA Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hCC hth hw hlen ε₁ ε₂ hε₁ hε₂
  have hmono : ∀ Cc : ℝ, Cc ≤ max C₁ C₂ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro Cc hC
    refine le_trans ?_ hth
    gcongr
  have hL := (h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hCC (hmono _ (le_max_left _ _)) hlen
    ε₁ ε₂ hε₁ hε₂).1
  obtain ⟨a₁, b₁, c₁⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₁ hε₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₂ hε₂
  have hR := tendsto_integral_inner_of_tendsto_eLpNorm_two _ _ _ _ _ _ _ a₁ a₂ b₁ b₂ c₁ c₂
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have hc : ∀ ε : ℝ, 0 < ε → KB.CptCoef p.T.base (fun g : B.Mat P.k P.r =>
      ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) •
        D.cutF p.T.base χ f ε g) := fun ε hε =>
    Formalism.FourierDecayAlt.P.PBE.cutCpt P p.T.base f χ ε
      (fun (n : ℕ) (g : B.Mat P.k P.r) =>
        ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ))
      hχ hε hf (fun _ _ => rfl) n
  exact (GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors hA Wp Wq P p Cb _ _ w hD (hc ε₁ hε₁) (hc ε₂ hε₂) hw).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectorsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  first | exact @GlobalTheory.beta_word_cutF_eq_integral_inner_tv | exact GlobalTheory.beta_word_cutF_eq_integral_inner_tv | (intros; apply GlobalTheory.beta_word_cutF_eq_integral_inner_tv <;> assumption)
end
end
