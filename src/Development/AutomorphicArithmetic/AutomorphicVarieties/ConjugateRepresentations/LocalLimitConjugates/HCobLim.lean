module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSolve

section

@[expose] public section

noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H


theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finsetSum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HCobLim

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def Fty {I : Type} (f : (I → ℂ) → ℂ) : Prop :=
  ∃ L : I →₀ ℂ, ∀ b : I → ℂ, Finsupp.linearCombination ℂ b L = f b

private theorem fty_ev {I : Type} (a : ℂ) (i : I) : Fty fun b : I → ℂ => a * b i :=
  ⟨Finsupp.single i a, fun b => by rw [Finsupp.linearCombination_single, smul_eq_mul]⟩

private theorem fty_sub {I : Type} {f g : (I → ℂ) → ℂ} (hf : Fty f) (hg : Fty g) : Fty fun b => f b - g b := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun b => by rw [map_sub, hL, hM]⟩

private theorem fty_sum {I K : Type} (t : Finset K) (f : K → (I → ℂ) → ℂ) (hf : ∀ k, Fty (f k)) :
    Fty fun b => ∑ k ∈ t, f k b := by
  choose L hL using hf
  exact ⟨∑ k ∈ t, L k, fun b => by rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hL k b⟩

private theorem fty_solve {I J : Type} (f : J → (I → ℂ) → ℂ) (hf : ∀ j, Fty (f j)) (c : J → ℂ) (cn : ℕ → J → ℂ)
    (h : ∀ k, ∃ b, ∀ j, f j b = cn k j) (hl : ∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) :
    ∃ b, ∀ j, f j b = c j := by
  choose L hL using hf
  have hs : ∀ (b : I → ℂ) j, (L j).sum (fun i x => x * b i) = f j b := by
    intro b j
    rw [← hL, Finsupp.linearCombination_apply]
    rfl
  obtain ⟨b, hb⟩ := absSolve I J L c cn (fun k => by
    obtain ⟨b, hb⟩ := h k
    exact ⟨b, fun j => by rw [hs, hb]⟩) hl
  exact ⟨b, fun j => by rw [← hs, hb]⟩

theorem UpperTheory.V.Cj.H.hCobLim :
    UpperTheory.V.Cj.H.HCobLim := by
  intro Γ S _ d ρ hρ q c cn h hl
  have hlim : ∀ x : List Γ, x.length = q + 1 → ∀ s i,
      Tendsto (fun k => (c - cn k) x s i) atTop (𝓝 (c x s i)) := by
    intro x hx s i
    have h1 : Tendsto (fun k => cn k x s i) atTop (𝓝 0) := tendsto_pi_nhds.1 (hl x hx s) i
    simpa using (tendsto_const_nhds (x := c x s i)).sub h1
  cases q with
  | zero =>
    intro x hx
    funext s i
    have h1 := hlim x hx s i
    have h2 : (fun k => (c - cn k) x s i) = fun _ => (0 : ℂ) := by
      funext k
      rw [h k x hx]
      rfl
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  | succ q =>
    let cur : (List Γ × S × Fin d → ℂ) → List Γ → S → Fin d → ℂ := fun b x s i => b (x, s, i)
    let f : (Γ × {x : List Γ // x.length = q + 1} × S × Fin d) ⊕ ({x : List Γ // x.length = q + 2} × S × Fin d) →
        (List Γ × S × Fin d → ℂ) → ℂ :=
      Sum.elim (fun p b => cur b (p.2.1.1.map (p.1 * ·)) p.2.2.1 p.2.2.2 - ρ p.1 (cur b p.2.1.1) p.2.2.1 p.2.2.2)
        (fun p b => hd (cur b) p.1.1 p.2.1 p.2.2)
    have hf : ∀ j, Fty (f j) := by
      rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
      · obtain ⟨s', B, hB⟩ := hρ γ s
        have e : f (Sum.inl (γ, x, s, i)) =
            fun b => 1 * b (x.1.map (γ * ·), s, i) - ∑ j, B i j * b (x.1, s', j) := by
          funext b
          simp only [f, Sum.elim_inl, hB, one_mul]
          rfl
        rw [e]
        exact fty_sub (fty_ev _ _) (fty_sum _ _ fun j => fty_ev _ _)
      · have e : f (Sum.inr (x, s, i)) =
            fun b => ∑ j ∈ Finset.range x.1.length, ((-1 : ℂ) ^ j) * b (x.1.eraseIdx j, s, i) := by
          funext b
          simp [f, cur, hd, Finset.sum_apply]
        rw [e]
        exact fty_sum _ _ fun j => fty_ev _ _
    obtain ⟨b, hb⟩ := fty_solve f hf (Sum.elim (fun _ => 0) fun p => c p.1.1 p.2.1 p.2.2)
      (fun k => Sum.elim (fun _ => 0) fun p => (c - cn k) p.1.1 p.2.1 p.2.2) (fun k => by
        obtain ⟨b, h1, h2⟩ := h k
        refine ⟨fun p => b p.1 p.2.1 p.2.2, ?_⟩
        rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
        · change b (x.1.map (γ * ·)) s i - ρ γ (b x.1) s i = 0
          rw [h1 γ x.1 x.2, sub_self]
        · change hd b x.1 s i = (c - cn k) x.1 s i
          rw [h2 x.1 x.2]) (by
        rintro (p | ⟨x, s, i⟩)
        · exact tendsto_const_nhds
        · exact hlim x.1 x.2 s i)
    refine ⟨cur b, fun γ x hx => ?_, fun x hx => ?_⟩
    · funext s i
      exact sub_eq_zero.1 (hb (Sum.inl (γ, ⟨x, hx⟩, s, i)))
    · funext s i
      exact (hb (Sum.inr (⟨x, hx⟩, s, i))).symm
end
end
