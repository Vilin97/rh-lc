module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasisSubsetOfSaturatedSubmoduleStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsDescendedRingHomOnQuotientStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermitianOrthogonalProjectionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPosDefFormOnQuotientStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRealOrthogonalProjectionOfRealGramStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentComplexOfRealHermitianStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemSpanOfRealCombinationPeriodsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentRealPeriodsBasis

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentRealPeriodsBasisStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.linearIndependent_real_periods_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeQuotientCompat

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_assemble_of_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  intro E _ _ _ g g' Λ Λ' _ _ _ _ R R₁ D π q Hm' B' hsurj hadd hsmul hker hB hHm hpos hform
  choose s hsD hs using hsurj
  have hwd : ∀ x ∈ D, ∀ y ∈ D, π x = π y → q (R.P x) = q (R.P y) := by
    intro x hx y hy hxy
    have hxy' : x - y ∈ D := D.sub_mem hx hy
    have h1 := hadd (x - y) hxy' y hy
    rw [sub_add_cancel, hxy] at h1
    have h2 : π (x - y) = 0 :=
      calc π (x - y) = π (x - y) + π y - π y := (add_sub_cancel_right _ _).symm
        _ = π y - π y := by rw [← h1]
        _ = 0 := sub_self _
    have h3 := hker _ hxy' h2
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  let P' : Λ' →+ (Fin g' → ℂ) := AddMonoidHom.mk' (fun x' => q (R.P (s x'))) (fun x' y' => by
    show q (R.P (s (x' + y'))) = q (R.P (s x')) + q (R.P (s y'))
    have hD : s x' + s y' ∈ D := D.add_mem (hsD x') (hsD y')
    have h := hwd _ (hsD (x' + y')) _ hD (by rw [hs, hadd _ (hsD x') _ (hsD y'), hs, hs])
    rw [h, map_add (f := _), map_add (f := _)])
  have hP' : ∀ x ∈ D, P' (π x) = q (R.P x) := fun x hx => hwd _ (hsD (π x)) _ hx (hs (π x))
  refine ⟨⟨R₁.1, R₁.2, R₁.3, R₁.form, R₁.5, R₁.6, R₁.7, P', Hm', hHm, hpos, ?_, B', ?_⟩, rfl, rfl, hP'⟩
  · intro x' y'
    have h := hform _ (hsD x') _ (hsD y')
    rw [hs, hs] at h
    exact h
  · intro a x'
    have hax : a • s x' ∈ D := (hsmul a _ (hsD x')).1
    have h1 : π (a • s x') = a • x' := by rw [(hsmul a _ (hsD x')).2, hs]
    calc P' (a • x') = P' (π (a • s x')) := by rw [h1]
      _ = q (R.P (a • s x')) := hP' _ hax
      _ = q (R.B a (R.P (s x'))) := by rw [R.14]
      _ = B' a (q (R.P (s x'))) := (hB a _).symm

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeQuotientCompatStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.riemannLattice_quotient_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem orth_of_set {m : ℕ} {T : Set (Fin m → ℂ)} {H : Matrix (Fin m) (Fin m) ℂ} {z : Fin m → ℂ}
    (h : ∀ t ∈ T, z ⬝ᵥ H *ᵥ star t = 0) : ∀ s ∈ Submodule.span ℂ T, z ⬝ᵥ H *ᵥ star s = 0 := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [star_add, mulVec_add, dotProduct_add, hx, hy]
  | smul a x _ hx => simp [star_smul, mulVec_smul, dotProduct_smul, hx]

theorem span_period (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) :
    Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (hI v).1 hv
    show R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i))
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y hx' hy' hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hx ((hI x).2 hx')) (hy ((hI y).2 hy'))
    | smul a x hx' hx =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ a (hx ((hI x).2 hx'))
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, (hI _).2 (Submodule.subset_span ⟨i, rfl⟩), rfl⟩

theorem im_quot (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e)) (hiso : IsIsoSub R.form I)
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) {g' : ℕ} (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hk : LinearMap.ker q = Submodule.span ℂ (R.P '' I)) (H' : Matrix (Fin g') (Fin g') ℂ)
    (hm : ∀ a b, (∀ v ∈ I, R.ip (R.P v) a = 0) → q b ⬝ᵥ H' *ᵥ star (q a) = b ⬝ᵥ R.Hm *ᵥ star a)
    {x y : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hy : ∀ v ∈ I, R.form y v = 0) :
    (q (R.P x) ⬝ᵥ H' *ᵥ star (q (R.P y))).im = R.form x y := by
  have heI : ∀ i, e i ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hui : ∀ i j, (R.P (e i) ⬝ᵥ R.Hm *ᵥ star (R.P (e j))).im = 0 := fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_real_orthogonal_projection_of_real_gram g k R.Hm R.pos _ hLI (GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI) hui (R.P y) (fun j => by
    rw [R.im, hy _ (heI j)]; simp)
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (e i) with hs
  have hsk : q s = 0 := by
    have : s ∈ LinearMap.ker q := by
      rw [hk, span_period R hI]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact this
  have hqy : q (R.P y - s) = q (R.P y) := by rw [map_sub, hsk, sub_zero]
  have horth : ∀ v ∈ I, R.ip (R.P v) (R.P y - s) = 0 := by
    intro v hv
    have hv' : R.P v ∈ Submodule.span ℂ (Set.range fun i => R.P (e i)) := by
      rw [← span_period R hI]; exact Submodule.subset_span ⟨v, hv, rfl⟩
    refine orth_of_set (T := Set.range fun i => R.P (e i)) ?_ _ hv'
    rintro _ ⟨j, rfl⟩
    exact hc j
  rw [← hqy, hm _ _ horth]
  have hxs : (R.P x ⬝ᵥ R.Hm *ᵥ star s).im = 0 := by
    simp only [hs, star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, Complex.im_sum, Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul, R.im,
      hx _ (heI _)]
    simp
  rw [star_sub, mulVec_sub, dotProduct_sub, Complex.sub_im, hxs, sub_zero, R.im]

theorem period_facts (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I) :
    LinearIndependent ℂ fun i => R.P (b (f i)) := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  refine GlobalTheory.T.linearIndependent_complex_of_real_hermitian g k R.Hm R.pos _ ((GlobalTheory.T.linearIndependent_real_periods_basis E g Λ R n b).comp f hf) fun i j => ?_
  rw [R.im, hiso _ (heI i) _ (heI j)]; simp

theorem exists_orth (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k : ℕ} {e : Fin k → Λ}
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range e))
    (hLI : LinearIndependent ℂ fun i => R.P (e i)) (z : Fin g → ℂ) :
    ∃ s ∈ Submodule.span ℂ (R.P '' I), ∀ v ∈ Submodule.span ℂ (R.P '' I), (z - s) ⬝ᵥ R.Hm *ᵥ star v = 0 := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI z
  rw [span_period R hI]
  refine ⟨∑ i, c i • R.P (e i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  refine orth_of_set ?_
  rintro _ ⟨j, rfl⟩
  exact hc j

theorem mem_of_mem_span (R : RiemLat E g Λ) {I : Submodule (𝓞 E) Λ} {k n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (f : Fin k → Fin n) (hf : Function.Injective f)
    (hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i))) (hiso : IsIsoSub R.form I)
    {x : Λ} (hx : ∀ v ∈ I, R.form x v = 0) (hs : R.P x ∈ Submodule.span ℂ (R.P '' I)) : x ∈ I := by
  have heI : ∀ i, b (f i) ∈ I := fun i => (hI _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hLI := period_facts R b f hf hI hiso
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_real_orthogonal_projection_of_real_gram g k R.Hm R.pos _ hLI (GlobalTheory.T.exists_hermitian_orthogonal_projection g k R.Hm R.pos _ hLI) (fun i j => by
    rw [R.im, hiso _ (heI i) _ (heI j)]; simp) (R.P x) (fun j => by rw [R.im, hx _ (heI j)]; simp)
  rw [span_period R hI] at hs
  set s : Fin g → ℂ := ∑ i, (c i : ℂ) • R.P (b (f i)) with hsdef
  have hsm : s ∈ Submodule.span ℂ (Set.range fun i => R.P (b (f i))) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw : R.P x - s = 0 := by
    by_contra hne
    have h0 : (R.P x - s) ⬝ᵥ R.Hm *ᵥ star (R.P x - s) = 0 :=
      orth_of_set (by rintro _ ⟨j, rfl⟩; exact hc j) _ (Submodule.sub_mem _ hs hsm)
    have := R.pos _ hne
    rw [h0] at this
    simp at this
  exact (hI x).2 (GlobalTheory.T.mem_span_of_real_combination_periods g k n Λ R.P b f (GlobalTheory.T.linearIndependent_real_periods_basis E g Λ R n b) hf x c (sub_eq_zero.1 hw))

end

theorem exists_univ_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  intro E _ _ _ g Λ _ _ R₀ I hsat hiso
  classical
  haveI := R₀.free
  haveI := R₀.fin
  obtain ⟨g', Λ', i1, i2, R₀', q₀, hq₀s, hq₀k, hq₀B, hq₀r, hq₀m⟩ := GlobalTheory.T.quotient_lattice_by_isotropic_submodule E g Λ Unit R₀ I hsat hiso
  obtain ⟨k, n, b, f, hf, hN⟩ := GlobalTheory.T.exists_basis_subset_of_saturated_submodule Λ (AddSubgroup.toIntSubmodule I.toAddSubgroup) (fun v m hm h => hsat v m hm h)
  have hI : ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := fun v => by
    rw [hN]; rfl
  have hLI₀ := period_facts R₀ b f hf hI hiso

  let D : AddSubgroup Λ :=
    { carrier := {x | ∀ y ∈ I, R₀.form x y = 0}
      add_mem' := fun {a c} ha hc y hy => by simp [ha y hy, hc y hy]
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by simp [ha y hy] }
  have hDmem : ∀ x, x ∈ D ↔ ∀ y ∈ I, R₀.form x y = 0 := fun x => Iff.rfl
  have hDsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D := by
    intro a x hx y hy
    rw [R₀.adj a (IsCMField.ringOfIntegersComplexConj E a) (by simp [IsCMField.coe_ringOfIntegersComplexConj])]
    exact hx _ (I.smul_mem _ hy)
  have hex : ∀ x ∈ D, ∃ x', R₀'.P x' = q₀ (R₀.P x) := by
    intro x hx
    have : q₀ (R₀.P x) ∈ Set.range R₀'.P := by
      rw [hq₀r]; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact this
  let π : Λ → Λ' := fun x => if h : x ∈ D then (hex x h).choose else 0
  have hπ : ∀ x ∈ D, R₀'.P (π x) = q₀ (R₀.P x) := by
    intro x h
    simp only [π, dif_pos h]
    exact (hex x h).choose_spec
  have hinj : Function.Injective R₀'.P := (GlobalTheory.T.riemann_lattice_eigen_projection E g' Λ' Unit R₀').1
  have hπs : ∀ x', ∃ x ∈ D, π x = x' := by
    intro x'
    have : R₀'.P x' ∈ Set.range R₀'.P := ⟨x', rfl⟩
    rw [hq₀r] at this
    obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := this
    exact ⟨x, hx, hinj ((hπ x hx).trans h)⟩
  have hπadd : ∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y := by
    intro x hx y hy
    apply hinj
    rw [hπ _ (D.add_mem hx hy), map_add (f := _), map_add (f := _), map_add (f := _), hπ x hx, hπ y hy]
  have hπsmul : ∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x := by
    intro a x hx
    refine ⟨hDsmul a x hx, hinj ?_⟩
    rw [hπ _ (hDsmul a x hx), R₀'.act, hπ x hx, R₀.act, hq₀B]
  have hπI : ∀ x ∈ D, π x = 0 → x ∈ I := by
    intro x hx h0
    have h1 : q₀ (R₀.P x) = 0 := by rw [← hπ x hx, h0, map_zero]
    have h2 : R₀.P x ∈ LinearMap.ker q₀ := h1
    rw [hq₀k] at h2
    exact mem_of_mem_span R₀ b f hf hI hiso hx h2
  have hπform : ∀ x ∈ D, ∀ y ∈ D, R₀'.form (π x) (π y) = R₀.form x y := by
    intro x hx y hy
    have h := im_quot R₀ hI hiso hLI₀ q₀ hq₀k R₀'.Hm (fun a c ha => hq₀m a c ha) hx hy
    rw [← hπ x hx, ← hπ y hy, R₀'.im] at h
    exact_mod_cast h
  have hk : k + g' = g := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q₀
    rw [LinearMap.range_eq_top.2 hq₀s, hq₀k, span_period R₀ hI, finrank_span_eq_card hLI₀] at h1
    simp at h1
    omega
  refine ⟨g', k, Λ', i1, i2, fun i => b (f i), R₀'.form, π, hk, hπs, fun R hR => ?_⟩
  have hiso' : IsIsoSub R.form I := hR ▸ hiso
  have hLI := period_facts R b f hf hI hiso'
  refine ⟨hLI, span_period R hI, fun q hqs hqk => ?_⟩
  obtain ⟨Hm', hherm, hpos, hmet⟩ := GlobalTheory.T.exists_posDef_form_on_quotient g g' R.Hm R.herm R.pos _ q hqs hqk (exists_orth R hI hLI)
  have hD' : ∀ x, (∀ y ∈ I, R.form x y = 0) → x ∈ D := fun x h => by rw [hDmem, ← hR]; exact h
  have hDR : ∀ x ∈ D, ∀ y ∈ I, R.form x y = 0 := fun x h => by rw [hR]; exact h
  have hmet' : ∀ a c, (∀ v ∈ I, R.ip (R.P v) a = 0) → q c ⬝ᵥ Hm' *ᵥ star (q a) = c ⬝ᵥ R.Hm *ᵥ star a := by
    intro a c ha
    refine hmet a c (orth_of_set ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact ha v hv
  have hqB : ∀ (a : 𝓞 E) z, q z = 0 → q (R.B a z) = 0 := by
    intro a z hz
    have hz' : z ∈ Submodule.span ℂ (R.P '' I) := by rw [← hqk]; exact hz
    clear hz
    have : R.B a z ∈ Submodule.span ℂ (R.P '' I) := by
      induction hz' using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, hv, rfl⟩ := hw
        rw [← R.act]
        exact Submodule.subset_span ⟨_, I.smul_mem _ hv, rfl⟩
      | zero => simp
      | add w w' _ _ h h' =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ h h'
      | smul c w _ h =>
        rw [map_smul]
        exact Submodule.smul_mem _ c h
    rw [← hqk] at this
    exact this
  have hker : ∀ x ∈ D, π x = 0 → q (R.P x) = 0 := by
    intro x hx h0
    have : R.P x ∈ LinearMap.ker q := by
      rw [hqk]; exact Submodule.subset_span ⟨x, hπI x hx h0, rfl⟩
    exact this
  have him : ∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₀'.form (π x) (π y) := by
    intro x hx y hy
    rw [im_quot R hI hiso' hLI q hqk Hm' hmet' (hDR x hx) (hDR y hy), hπform x hx y hy, hR]
  obtain ⟨B', hB'⟩ := GlobalTheory.T.exists_descended_ringHom_on_quotient (𝓞 E) g g' R.B q hqs hqB
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.T.riemannLattice_quotient_compat E g g' Λ Λ' R R₀' D π q Hm' B' hπs hπadd hπsmul hker hB' hherm hpos him
  refine ⟨R', h1, fun x hx => h3 x (hD' x hx), fun x y hx => ?_⟩
  show q y ⬝ᵥ R'.Hm *ᵥ star (q x) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [h2]
  exact hmet' x y hx

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructureStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.isotropic_quotient_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot <;> assumption)
end
end
