module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEvalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffEqZeroOfEvalEqComulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnectedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartGroupLawEvalRightUnitStatement
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveEvalTmulStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEq

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEqStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.eval_swap_eq' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  first | exact @GlobalTheory.CommSwap.eval_swap_eq | exact GlobalTheory.CommSwap.eval_swap_eq | (intros; apply GlobalTheory.CommSwap.eval_swap_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCast

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.FinProjComplete

theorem mem_span_pow_smul_top_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M) ↔ ∃ m : M, x = (p ^ n : ℕ) • m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

theorem smodEq_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M))] ↔
      ∃ m : M, x - y = (p ^ n : ℕ) • m := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]

end GlobalTheory.FinProjComplete

open GlobalTheory.FinProjComplete in
theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective <;> assumption
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartEx

theorem isEval_comp {p : ℕ} {O A A' σ : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A]
    [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] A')
    (h : IsEval p x E) : IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨a, ha⟩ := hN f hf
  exact ⟨φ a, by rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]⟩

theorem nil_map {p : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {a : A}
    (h : ∃ N : ℕ, (p : A) ∣ a ^ N) : ∃ N : ℕ, (p : A') ∣ φ a ^ N := by
  obtain ⟨N, b, hb⟩ := h
  exact ⟨N, φ b, by rw [← map_pow, hb, map_mul, map_natCast]⟩

theorem eq_zero_of_dvd {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {c : O} (h : ∀ m : ℕ, (p : O) ^ m ∣ c) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun m => ?_
  obtain ⟨b, hb⟩ := h m
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, hb⟩

theorem eq_zero_of_ker {p : ℕ} {O σ : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {A : ℕ → Type} [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)]
    (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hker : ∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f)
    {f : MvPowerSeries σ O} (hf : ∀ n, E n f = 0) : f = 0 := by
  ext α
  rw [map_zero]
  refine eq_zero_of_dvd (p := p) fun m => ?_
  obtain ⟨n, hn⟩ := hker m (α.degree + 1)
  exact hn f (hf n) α (Nat.lt_succ_self _)

theorem chart_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, ev, hnil, hev, hres, haug, hsurj, hker⟩ := GlobalTheory.T.exists_coordinates_of_isConnected p C v O hv G hG
  have hc2 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hc3 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] (G.A n ⊗[O] G.A n))})
      (G.A n ⊗[O] (G.A n ⊗[O] G.A n)) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hcA : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have nil2 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) j ^ N := by
    rintro n (i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
    · simpa using nil_map (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
  have nil3 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] (G.A n ⊗[O] G.A n)) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) j ^ N := by
    rintro n (i | i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
  have hE2 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n,
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) E := by
    intro n
    haveI := hc2 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.exists
  choose E₂ hE₂ using hE2
  have hE3 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n),
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) E := by
    intro n
    haveI := hc3 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil3 n)).1.exists
  choose E₃ hE₃ using hE3
  have hsurj2 : ∀ n, Function.Surjective (E₂ n) := fun n => by
    haveI := hc2 n
    exact GlobalTheory.T.surjective_isEval_tmul_of_surjective p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n)
  have hker2 : ∀ m N : ℕ, ∃ n, ∀ f, E₂ n f = 0 → ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn⟩
  have hker3 : ∀ m N : ℕ, ∃ n, ∀ f, E₃ n f = 0 → ∀ α : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    have hn2 := GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn
    have hpt : (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) fun j => (1 : G.A n) ⊗ₜ[O] (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] x n i) j)) = (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) := by
      funext j
      rcases j with j | j | j <;> rfl
    have hE3' := hE₃ n
    rw [← hpt] at hE3'
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) _ (ev n) (E₂ n) (E₃ n) m N (hev n) (hE₂ n) hE3' (hsurj n) (hsurj2 n) hn hn2⟩
  have hstep : ∀ i n f, E₂ (n + 1) f = Coalgebra.comul (R := O) (x (n + 1) i) →
      E₂ n f = Coalgebra.comul (R := O) (x n i) := by
    intro i n f hf
    let ρ : G.A (n + 1) ⊗[O] G.A (n + 1) →ₐ[O] G.A n ⊗[O] G.A n :=
      Algebra.TensorProduct.map (AlgHomClass.toAlgHom (G.res n)) (AlgHomClass.toAlgHom (G.res n))
    have hρ : ρ.comp (E₂ (n + 1)) = E₂ n := by
      haveI := hc2 n
      refine (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.unique ?_ (hE₂ n)
      have h1 := isEval_comp ρ (hE₂ (n + 1))
      convert h1 using 1
      funext j
      rcases j with j | j <;> simp [ρ, AlgHomClass.toAlgHom, hres]
    rw [← hρ, AlgHom.comp_apply, hf]
    exact (CoalgHomClass.map_comp_comul_apply (G.res n) (x (n + 1) i)).trans (by rw [hres])
  have hμ : ∀ i, ∃ g, ∀ n, E₂ n g = Coalgebra.comul (R := O) (x n i) := by
    intro i
    exact GlobalTheory.T.exists_series_of_compatible' p O (Fin d ⊕ Fin d) (fun n => G.A n ⊗[O] G.A n) (fun n => (hc2 n).toIsHausdorff) _ E₂
      (fun n => Coalgebra.comul (R := O) (x n i)) hE₂ (fun n => hsurj2 n _) (hstep i) hker2
  choose μ hμ using hμ
  have hconst : ∀ i, constantCoeff (μ i) = 0 :=
    GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' p O (G.A 0) (x 0) (E₂ 0) μ (haug 0) (hE₂ 0) (fun i => hμ i 0)
  refine ⟨d, ⟨⟨x, ev, E₂, μ, hnil, hev, hE₂, hres, haug, hsurj, hker, ?_, fun n i => hμ i n⟩⟩⟩
  refine ⟨hconst, ?_, fun i => ?_, ?_⟩
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) ev hker fun n => ?_)
    haveI := hcA n
    rw [map_sub, GlobalTheory.T.formalChart_groupLaw_eval_right_unit p O (G.A n) (x n) (ev n) (E₂ n) μ (hnil n) (haug n) (hev n) (hE₂ n) (fun i => hμ i n) i,
      (hev n).1 i, sub_self]
  · refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₂ hker2 fun n => ?_)
    haveI := hc2 n
    rw [map_sub, GlobalTheory.T.eval_swap_eq' p O (G.A n) (x n) (E₂ n) μ (hnil n) (hE₂ n) (fun i => hμ i n) i, sub_self]
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₃ hker3 fun n => ?_)
    haveI := hc3 n
    rw [map_sub, GlobalTheory.T.isEval_comul_assoc_of_isEval p O (G.A n) (x n) (E₂ n) (E₃ n) μ (hnil n) hconst (hE₂ n) (hE₃ n) (fun i => hμ i n) i, sub_self]

end GlobalTheory.ChartEx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnectedStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_pDivGroupFormalChart_of_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  first | exact @GlobalTheory.ChartEx.chart_exists | exact GlobalTheory.ChartEx.chart_exists | (intros; apply GlobalTheory.ChartEx.chart_exists <;> assumption)
end
end
