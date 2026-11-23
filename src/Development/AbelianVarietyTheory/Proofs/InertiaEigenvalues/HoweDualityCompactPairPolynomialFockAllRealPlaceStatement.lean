module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJointHarmonicOfLoweringStableSubmodule
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.DualLattices.FischerSmulRight
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryBasisGeneralLinearSeriesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJointHarmonicOfLoweringStableSubmoduleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.exists_jointHarmonic_of_lowering_stable_submodule : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  first | exact @GlobalTheory.LowerHarm.lower_to_harmonic | exact GlobalTheory.LowerHarm.lower_to_harmonic | (intros; apply GlobalTheory.LowerHarm.lower_to_harmonic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonicsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.fockTargetGlAction_compact_preserves_jointHarmonics : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  first | exact @GlobalTheory.CompactHarm.fockT_compact_harm | exact GlobalTheory.CompactHarm.fockT_compact_harm | (intros; apply GlobalTheory.CompactHarm.fockT_compact_harm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonics

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.RaiseGen

open MvPolynomial GlobalTheory.FockIsotypic

theorem exists_ker_add_range {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (A : E →ₗ[ℂ] E)
    (h : ∀ x, A (A x) = 0 → A x = 0) (x : E) : ∃ x₀ y, A x₀ = 0 ∧ x = x₀ + A y := by
  have hd : Disjoint (LinearMap.ker A) (LinearMap.range A) := by
    rw [Submodule.disjoint_def]
    rintro _ hz ⟨y, rfl⟩
    exact h y hz
  have ht : LinearMap.ker A ⊔ LinearMap.range A = ⊤ :=
    Submodule.eq_top_of_disjoint _ _ (by have := LinearMap.finrank_range_add_finrank_ker A; omega) hd
  obtain ⟨x₀, h0, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (ht ▸ Submodule.mem_top (x := x))
  exact ⟨x₀, y, h0, e.symm⟩

theorem mem_of_filtration {V W K ι : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Fintype ι] (act : K → V →ₗ[ℂ] V) (ρ : K → W →ₗ[ℂ] W) (R L : ι → V →ₗ[ℂ] V)
    (S : ℕ → Submodule ℂ V) [∀ d, FiniteDimensional ℂ (S d)]
    (hR : ∀ i k x, act k (R i x) = R i (act k x)) (hL : ∀ i k x, act k (L i x) = L i (act k x))
    (hL0 : ∀ i, ∀ x ∈ S 0, L i x = 0) (hLs : ∀ i d, ∀ x ∈ S (d + 1), L i x ∈ S d)
    (hRL : ∀ i d, ∀ x ∈ S d, R i (L i x) ∈ S d)
    (hker : ∀ x, ∑ i, R i (L i x) = 0 → ∀ i, L i x = 0)
    (hAA : ∀ x, (∀ j, L j (∑ i, R i (L i x)) = 0) → ∑ i, R i (L i x) = 0)
    (N : Submodule ℂ (W →ₗ[ℂ] V))
    (hN0 : ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w i, L i (φ w) = 0) → φ ∈ N)
    (hNR : ∀ ψ ∈ N, ∀ i, R i ∘ₗ ψ ∈ N) (d : ℕ) :
    ∀ φ : W →ₗ[ℂ] V, (∀ k w, φ (ρ k w) = act k (φ w)) → (∀ w, φ w ∈ S d) → φ ∈ N := by
  induction d with
  | zero => exact fun φ hφ hS => hN0 φ hφ fun w i => hL0 i _ (hS w)
  | succ d ih =>
    intro φ hφ hS
    let E : Submodule ℂ (W →ₗ[ℂ] V) :=
      { carrier := {ψ | (∀ k w, ψ (ρ k w) = act k (ψ w)) ∧ ∀ w, ψ w ∈ S (d + 1)}
        add_mem' := fun {a b} ha hb => ⟨fun k w => by simp [ha.1, hb.1], fun w => add_mem (ha.2 w) (hb.2 w)⟩
        zero_mem' := ⟨fun k w => by simp, fun w => zero_mem _⟩
        smul_mem' := fun c a ha => ⟨fun k w => by simp [ha.1], fun w => Submodule.smul_mem _ c (ha.2 w)⟩ }
    haveI : FiniteDimensional ℂ E := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (LinearMap.compRight (M := W) ℂ (S (d + 1)).subtype)) ?_
      intro ψ hψ
      exact ⟨ψ.codRestrict _ hψ.2, rfl⟩
    let A : V →ₗ[ℂ] V := ∑ i, R i ∘ₗ L i
    have hA : ∀ x, A x = ∑ i, R i (L i x) := fun x => by simp [A, LinearMap.sum_apply]
    have hE : ∀ ψ ∈ E, LinearMap.compRight (M := W) ℂ A ψ ∈ E := fun ψ hψ =>
      ⟨fun k w => by
        change A (ψ (ρ k w)) = act k (A (ψ w))

        simp only [hA, hψ.1, map_sum, hR, hL], fun w => by
        change A (ψ w) ∈ _
        rw [hA]
        exact Submodule.sum_mem _ fun i _ => hRL i _ _ (hψ.2 w)⟩
    obtain ⟨φ₀, ψ, h0, e⟩ := exists_ker_add_range ((LinearMap.compRight (M := W) ℂ A).restrict hE) (fun ψ h => by
      refine Subtype.ext (LinearMap.ext fun w => ?_)
      have h1 : A (A (ψ.1 w)) = 0 := LinearMap.congr_fun (congrArg Subtype.val h) w
      change A (ψ.1 w) = 0
      rw [hA] at h1
      have h2 := hker _ h1
      rw [hA] at h2 ⊢
      exact hAA _ h2) ⟨φ, hφ, hS⟩
    have e' : φ = φ₀.1 + ∑ i, R i ∘ₗ (L i ∘ₗ ψ.1) := by
      refine LinearMap.ext fun w => ?_
      have h1 : φ w = φ₀.1 w + A (ψ.1 w) := LinearMap.congr_fun (congrArg Subtype.val e) w
      rw [h1, hA]
      simp [LinearMap.sum_apply]
    rw [e']
    refine add_mem (hN0 _ φ₀.2.1 fun w => hker _ ?_) (Submodule.sum_mem _ fun i _ => hNR _ (ih _ ?_ ?_) i)
    · rw [← hA]
      exact LinearMap.congr_fun (congrArg Subtype.val h0) w
    · intro k w
      simp only [LinearMap.comp_apply, ψ.2.1, hL]
    · exact fun w => hLs i d _ (ψ.2.2 w)

section Fischer

variable {σ : Type} [Fintype σ]

theorem fis_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) : fis (X v * P) Q = fis P (pderiv v Q) := by
  classical
  unfold fis
  rw [mul_comm, map_mul, rename_X, ReciprocityTheory.PGsh.fischer_mul_X, pderiv_rename (flat σ).injective]

theorem fis_sum_left {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fis (∑ i ∈ s, f i) Q = ∑ i ∈ s, fis (f i) Q := by
  unfold fis

  rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_left]

theorem fis_sum_right {α : Type} (s : Finset α) (P : MvPolynomial σ ℂ) (f : α → MvPolynomial σ ℂ) :
    fis P (∑ i ∈ s, f i) = ∑ i ∈ s, fis P (f i) := by
  unfold fis

  rw [map_sum, ReciprocityTheory.PGsh.fischer_sum_right]

theorem fis_zero_left (Q : MvPolynomial σ ℂ) : fis 0 Q = 0 := by
  simpa using fis_smul_left 0 0 Q

theorem fis_zero_right (P : MvPolynomial σ ℂ) : fis P 0 = 0 := by
  simpa using fis_smul_right 0 P 0

theorem fis_neg_right (P Q : MvPolynomial σ ℂ) : fis P (-Q) = -fis P Q := by
  simpa using fis_smul_right (-1) P Q

theorem eq_zero_of_fis_re (P : MvPolynomial σ ℂ) (h : (fis P P).re = 0) : P = 0 := by
  by_contra hP
  exact fis_self_ne_zero hP (Complex.ext h (Complex.conj_eq_iff_im.1 (fis_conj P P)))

variable {ι : Type} [Fintype ι] (R L : ι → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
  (hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q))

include hadj

theorem lower_eq_zero (P : MvPolynomial σ ℂ) (h : ∑ i, R i (L i P) = 0) (i : ι) : L i P = 0 := by
  have h1 : fis (∑ i, R i (L i P)) P = 0 := by rw [h, fis_zero_left]
  rw [fis_sum_left] at h1
  simp only [hadj, Finset.sum_neg_distrib, neg_eq_zero] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, Complex.zero_re,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => fis_self_re_nonneg _] at h2
  exact eq_zero_of_fis_re _ (h2 i (Finset.mem_univ i))

theorem sum_eq_zero_of_lower (P : MvPolynomial σ ℂ) (h : ∀ j, L j (∑ i, R i (L i P)) = 0) :
    ∑ i, R i (L i P) = 0 := by
  refine eq_zero_of_fis_re _ ?_
  rw [fis_sum_left]
  simp only [hadj, h, fis_zero_right, neg_zero, Finset.sum_const_zero, Complex.zero_re]

end Fischer

theorem fockT_raise {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = ∑ j : Fin n, X (τ, i, j) * (X (τ, l, j) * P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((l : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((i : ℕ) < p τ) = true := decide_eq_true hi
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem raise_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : (i : ℕ) < p τ) (hl : p τ ≤ (l : ℕ)) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k + 2 := by
  rw [fockT_raise τ p i l hi hl]
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
  have := totalDegree_mul (X (τ, l, j) : PolF D m n) P
  rw [totalDegree_X] at this ⊢
  omega

theorem mem_of_raise : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  intro D n m w BS K _ r _ W _ _ _ ρ N hN0 hNR φ hφ
  classical
  let ι : Type := {t : D.what₂.Tau × Fin m × Fin m // (t.2.1 : ℕ) < w.p t.1 ∧ w.p t.1 ≤ (t.2.2 : ℕ)}
  let T : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ → PolF D m n →ₗ[ℂ] PolF D m n := fun τ Y =>
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Y
  let R : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.1 t.1.2.2 1)
  let L : ι → PolF D m n →ₗ[ℂ] PolF D m n := fun t => T t.1.1 (Matrix.single t.1.2.2 t.1.2.1 1)
  have hT : ∀ τ Y k x, GlobalTheory.ExportSeries.fockGL m w BS (r k) (T τ Y x) =
      T τ Y (GlobalTheory.ExportSeries.fockGL m w BS (r k) x) := fun τ Y k x => by
    rw [GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
    exact congrArg _ (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ Y x)
  have hadj : ∀ i P Q, fis (R i P) Q = -fis P (L i Q) := fun t P Q => by
    simp only [R, L, T]
    rw [fockT_raise _ _ _ _ t.2.1 t.2.2, GlobalTheory.LowerHarm.fockT_lower _ _ _ _ t.2.2 t.2.1, fis_neg_right, neg_neg,
      fis_sum_left, fis_sum_right]
    exact Finset.sum_congr rfl fun j _ => by rw [fis_X_mul, fis_X_mul]
  have hdeg : ∃ d, ∀ w', (φ w').totalDegree ≤ d := by
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (φ (b j)).totalDegree, fun w' => ?_⟩

    rw [← b.sum_repr w', map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (φ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨d, hd⟩ := hdeg
  refine mem_of_filtration (fun k => GlobalTheory.ExportSeries.fockGL m w BS (r k)) (fun k => ρ k) R L
    (fun d => restrictTotalDegree (FVar D m n) ℂ d) (fun t => hT _ _) (fun t => hT _ _) ?_ ?_ ?_
    (lower_eq_zero R L hadj) (sum_eq_zero_of_lower R L hadj) N ?_ ?_ d φ hφ
    fun w' => (mem_restrictTotalDegree _ _ _).2 (hd w')
  · intro t x hx
    rw [mem_restrictTotalDegree] at hx
    exact GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    exact GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k (by omega)
  · intro t k x hx
    rw [mem_restrictTotalDegree] at hx ⊢
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : L t x = 0 := GlobalTheory.LowerHarm.lower_zero _ _ _ _ t.2.2 t.2.1 x (by omega)
      simp [this]
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact raise_deg _ _ _ _ t.2.1 t.2.2 _ k (GlobalTheory.LowerHarm.lower_deg _ _ _ _ t.2.2 t.2.1 x k hx)
  · exact fun ψ hψ h => hN0 ψ hψ fun w' τ i l hi hl => h w' ⟨(τ, l, i), hl, hi⟩
  · exact fun ψ hψ t => hNR ψ hψ _ _ _ t.2.1 t.2.2

end GlobalTheory.RaiseGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonicsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.mem_of_raisingOperators_jointHarmonics : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  first | exact @GlobalTheory.RaiseGen.mem_of_raise | exact GlobalTheory.RaiseGen.mem_of_raise | (intros; apply GlobalTheory.RaiseGen.mem_of_raise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
namespace GlobalTheory.HoweCompactAlg

theorem mem_of_equivariant : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ M : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ M, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin m) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ M := by
  intro D n m w BS K _ r hU hOnto W _ _ _ ρ hρ M hMeq hMT hM0 φ hφ
  obtain ⟨ψ, hψM, hψ0, hψH⟩ := GlobalTheory.T.exists_jointHarmonic_of_lowering_stable_submodule D n m w.p W M (fun ψ hψ τ i l _ _ => hMT ψ hψ τ _) hM0
  let S : Submodule ℂ (W →ₗ[ℂ] PolF D m n) :=
    { carrier := {ψ | ψ ∈ M ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨M.add_mem ha hb, fun w' τ' i l h1 h2 => ?_⟩
        simp [LinearMap.add_apply, map_add (f := _), ha' w' τ' i l h1 h2, hb' w' τ' i l h1 h2]
      zero_mem' := ⟨M.zero_mem, fun w' τ' i l _ _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨M.smul_mem c ha, fun w' τ' i l h1 h2 => ?_⟩
        simp [LinearMap.smul_apply, map_smul, ha' w' τ' i l h1 h2] }
  have hS : ∀ φ' : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ' (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ' w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ' w') = 0) → φ' ∈ S := by
    refine GlobalTheory.T.unitary_basis_general_linear_series D n m w BS K r hU hOnto W ρ hρ S (fun ψ' h => hMeq ψ' h.1) (fun ψ' h => h.2) ?_ ?_
    · intro ψ' h τ a b hab
      refine ⟨hMT ψ' h.1 τ _, fun w' => ?_⟩
      exact GlobalTheory.T.fockTargetGlAction_compact_preserves_jointHarmonics D n m w.p (ψ' w') (h.2 w') τ a b hab
    · intro h
      apply hψ0
      have : ψ ∈ S := ⟨hψM, hψH⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
  exact GlobalTheory.T.mem_of_raisingOperators_jointHarmonics D n m w BS K r hU W ρ M (fun φ' h1 h2 => (hS φ' h1 h2).1)
    (fun ψ' h τ i l _ _ => hMT ψ' h τ _) φ hφ

end GlobalTheory.HoweCompactAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ M : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ M, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin m) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ M := by
  first | exact @GlobalTheory.HoweCompactAlg.mem_of_equivariant | exact GlobalTheory.HoweCompactAlg.mem_of_equivariant | (intros; apply GlobalTheory.HoweCompactAlg.mem_of_equivariant <;> assumption)
end
end
