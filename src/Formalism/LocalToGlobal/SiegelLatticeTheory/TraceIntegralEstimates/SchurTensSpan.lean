module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensRep

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def IsTensAbs (σ : ∀ v, G v → (H v →L[ℂ] H v)) (σs : (∀ v, G v) → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) : Prop :=
  (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) ∧ (∀ g x, σs g (tens x) = tens fun v => σ v (g v) (x v)) ∧
    Dense (Submodule.span ℂ (Set.range tens) : Set Hs)

variable {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

theorem continuous_tens (h : IsTensAbs σ σs tens) : Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x0
  set F : (∀ v, H v) → ℝ := fun x => RCLike.re (∏ v, ⟪x v, x v⟫_ℂ) -
    2 * RCLike.re (∏ v, ⟪x v, x0 v⟫_ℂ) + RCLike.re (∏ v, ⟪x0 v, x0 v⟫_ℂ) with hF
  have hFc : Continuous F := by fun_prop
  have hnorm : ∀ x, ‖tens x - tens x0‖ = Real.sqrt (F x) := by
    intro x
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      norm_sq_eq_re_inner (𝕜 := ℂ), h.1, h.1, h.1]
  have hF0 : F x0 = 0 := by simp only [hF]; ring
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have h2 : Tendsto (fun x => Real.sqrt (F x)) (𝓝 x0) (𝓝 (Real.sqrt (F x0))) :=
    (Real.continuous_sqrt.comp hFc).tendsto x0
  rw [hF0, Real.sqrt_zero] at h2
  exact h2

theorem tens_unit (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a : Hs) (x : ∀ v, H v) :
    ⟪σs g (tens x), σs g a⟫_ℂ = ⟪tens x, a⟫_ℂ := by
  have hS : ∀ b ∈ Submodule.span ℂ (Set.range tens), ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      rw [h.2.1, h.2.1, h.1, h.1]
      exact Finset.prod_congr rfl fun v _ => (hσ v).2.2.1 (g v) (x v) (y v)
    | zero => simp
    | add b c _ _ hb hc => rw [map_add (f := _), inner_add_right, inner_add_right, hb, hc]
    | smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]
  have hcl : IsClosed {b : Hs | ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ} :=
    isClosed_eq (continuous_const.inner (σs g).continuous) (continuous_const.inner continuous_id)
  have hsub := closure_minimal (fun b hb => hS b hb) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

theorem tens_unit_all (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a b : Hs) :
    ⟪σs g a, σs g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  have hS : ∀ c ∈ Submodule.span ℂ (Set.range tens), ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, rfl⟩ := hc
      exact tens_unit hσ h g b x
    | zero => simp
    | add c d _ _ hc hd => rw [map_add (f := _), inner_add_left, inner_add_left, hc, hd]
    | smul t c _ hc => rw [map_smul, inner_smul_left, inner_smul_left, hc]
  have hcl : IsClosed {c : Hs | ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ} :=
    isClosed_eq ((σs g).continuous.inner continuous_const) (continuous_id.inner continuous_const)
  have hsub := closure_minimal (fun c hc => hS c hc) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

theorem isUnitRep_tens (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) : IsUnitRep σs := by
  have hnorm : ∀ g c, ‖σs g c‖ = ‖c‖ := by
    intro g c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tens_unit_all hσ h g c c]
  have hspan : ∀ b ∈ Submodule.span ℂ (Set.range tens), Continuous fun g => σs g b := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨x, rfl⟩ := hb
      have e : (fun g => σs g (tens x)) = fun g => tens (fun v => σ v (g v) (x v)) :=
        funext fun g => h.2.1 g x
      rw [e]
      exact (continuous_tens h).comp (continuous_pi fun v => ((hσ v).2.2.2 (x v)).comp (continuous_apply v))
    | zero => simp only [map_zero]; exact continuous_const
    | add b c _ _ hb hc => simp only [map_add (f := _)]; exact hb.add hc
    | smul t b _ hb => simp only [map_smul]; exact hb.const_smul t
  refine ⟨?_, ?_, fun g a b => tens_unit_all hσ h g a b, ?_⟩
  · apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [h.2.1]
    simp only [ContinuousLinearMap.one_apply]
    congr 1
    funext v
    show σ v 1 (x v) = x v
    rw [(hσ v).1]
    rfl
  · intro g g'
    apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.mul_apply, h.2.1, h.2.1, h.2.1]
    congr 1
    funext v
    show σ v (g v * g' v) (x v) = σ v (g v) (σ v (g' v) (x v))
    rw [(hσ v).2.1]
    rfl
  · intro a
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hab⟩ := h.2.2.exists_dist_lt a (by positivity : (0 : ℝ) < ε / 3)
    have hc := Metric.tendsto_nhds.mp ((hspan b hb).tendsto g0) (ε / 3) (by positivity)
    filter_upwards [hc] with g hg
    have h1 : dist (σs g a) (σs g b) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]
    have h2 : dist (σs g0 b) (σs g0 a) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, norm_sub_rev]
    calc dist (σs g a) (σs g0 a)
        ≤ dist (σs g a) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 a) :=
          dist_triangle4 _ _ _ _
      _ < ε := by rw [h1, h2]; linarith

end Formalism.L2.S.Pv.SchurTens
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensSpan

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

section Gen

variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def SP (m : Measure K) (σs : K → (Hs →L[ℂ] Hs)) (D : ℝ) (a b a' b' : Hs) : Prop :=
  Integrable (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) m ∧
    ∫ x, ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ ∂m = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ)

variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem integrable_conj' {f : K → ℂ} (hf : Integrable f m) : Integrable (fun x => conj (f x)) m := by
  exact hf.mono (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by simp)

theorem SP_swap {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a' b' a b := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b', σs x a'⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => conj (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_mul, Complex.conj_conj]
    ring
  rw [e]
  refine ⟨integrable_conj' h.1, ?_⟩
  rw [integral_conj, h.2]
  rw [map_div₀, map_mul, Complex.conj_ofReal, inner_conj_symm, inner_conj_symm]

theorem SP_zero_a (b a' b' : Hs) : SP m σs D 0 b a' b' := by
  unfold SP
  simp

theorem SP_add_a {a₁ a₂ b a' b' : Hs} (h₁ : SP m σs D a₁ b a' b') (h₂ : SP m σs D a₂ b a' b') :
    SP m σs D (a₁ + a₂) b a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b, σs x (a₁ + a₂)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b, σs x a₁⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b, σs x a₂⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [map_add (f := _), inner_add_right, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_right]
  ring

theorem SP_smul_a (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D (c • a) b a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b, σs x (c • a)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_smul, inner_smul_right, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul c, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_right]
  ring

theorem SP_zero_b (a a' b' : Hs) : SP m σs D a 0 a' b' := by
  unfold SP
  simp

theorem SP_add_b {a b₁ b₂ a' b' : Hs} (h₁ : SP m σs D a b₁ a' b') (h₂ : SP m σs D a b₂ a' b') :
    SP m σs D a (b₁ + b₂) a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b₁ + b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b₁, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [inner_add_left, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_left]
  ring

theorem SP_smul_b (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a (c • b) a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪c • b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => conj c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [inner_smul_left, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_left]
  ring

private theorem mem_span_of_closed_lemma {P : Hs → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x)) {E : Set Hs} (hE : ∀ a ∈ E, P a) :
    ∀ a ∈ Submodule.span ℂ E, P a := by
  intro a ha
  let S : Submodule ℂ Hs :=
    { carrier := {x | P x}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsmul c x hx }
  have hle : Submodule.span ℂ E ≤ S := Submodule.span_le.mpr fun x hx => hE x hx
  exact hle ha

theorem SP_span {E : Set Hs} (h : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') :
    ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ Submodule.span ℂ E,
      ∀ b' ∈ Submodule.span ℂ E, SP m σs D a b a' b' := by
  have s1 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b' :=
    mem_span_of_closed_lemma (P := fun a => ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun b _ a' _ b' _ => SP_zero_a b a' b')
      (fun x y hx hy b hb a' ha' b' hb' => SP_add_a (hx b hb a' ha' b' hb') (hy b hb a' ha' b' hb'))
      (fun c x hx b hb a' ha' b' hb' => SP_smul_a c (hx b hb a' ha' b' hb'))
      (fun a ha => h a ha)
  have s2 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ E, ∀ b' ∈ E,
      SP m σs D a b a' b' := by
    intro a ha
    exact mem_span_of_closed_lemma (P := fun b => ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun a' _ b' _ => SP_zero_b a a' b')
      (fun x y hx hy a' ha' b' hb' => SP_add_b (hx a' ha' b' hb') (hy a' ha' b' hb'))
      (fun c x hx a' ha' b' hb' => SP_smul_b c (hx a' ha' b' hb'))
      (fun b hb => s1 a ha b hb)
  have s3 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E,
      SP m σs D a' b' a b :=
    mem_span_of_closed_lemma
      (P := fun a' => ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun b' _ a _ b _ => SP_zero_a b' a b)
      (fun x y hx hy b' hb' a ha b hb => SP_add_a (hx b' hb' a ha b hb) (hy b' hb' a ha b hb))
      (fun c x hx b' hb' a ha b hb => SP_smul_a c (hx b' hb' a ha b hb))
      (fun a' ha' b' hb' a ha b hb => SP_swap (s2 a ha b hb a' ha' b' hb'))
  have s4 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ Submodule.span ℂ E, ∀ a ∈ Submodule.span ℂ E,
      ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b := by
    intro a' ha'
    exact mem_span_of_closed_lemma
      (P := fun b' => ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun a _ b _ => SP_zero_b a' a b)
      (fun x y hx hy a ha b hb => SP_add_b (hx a ha b hb) (hy a ha b hb))
      (fun c x hx a ha b hb => SP_smul_b c (hx a ha b hb))
      (fun b' hb' => s3 a' ha' b' hb')
  intro a ha b hb a' ha' b' hb'
  exact SP_swap (s4 a' ha' b' hb' a ha b hb)

end Gen

section Pure

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

theorem SP_pure (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (d : ι → ℝ)
    (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs tens) (α β α' β' : ∀ v, H v) :
    SP (Measure.pi μ) σs (∏ v, d v) (tens α) (tens β) (tens α') (tens β') := by
  have hf : (fun x => ⟪tens β, σs x (tens α)⟫_ℂ * conj ⟪tens β', σs x (tens α')⟫_ℂ) =
      fun x => ∏ v, (⟪β v, σ v (x v) (α v)⟫_ℂ * conj ⟪β' v, σ v (x v) (α' v)⟫_ℂ) := by
    funext x
    rw [h.2.1, h.2.1, h.1, h.1, map_prod, ← Finset.prod_mul_distrib]
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact Integrable.fintype_prod_dep fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).1
  · rw [hf, integral_fintype_prod_eq_prod (fun v y => ⟪β v, σ v y (α v)⟫_ℂ * conj ⟪β' v, σ v y (α' v)⟫_ℂ)]
    simp only [fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).2]
    rw [h.1, h.1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Complex.ofReal_prod]

end Pure

end Formalism.L2.S.Pv.SchurTens
end
end
end
