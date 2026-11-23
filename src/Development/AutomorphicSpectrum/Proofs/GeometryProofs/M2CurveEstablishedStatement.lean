module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEigenSubDegreeEqStatement
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDualStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExistsStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegreeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeSumEigenSubDegrees

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeSumEigenSubDegreesStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_sum_eigen_sub_degrees : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen | exact GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LmuNumNonneg

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Crv.Chain

open GlobalTheory.CompanionTheory.Ar.Crv

theorem abel_bound (ν v : ℕ → ℝ) (P : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hν : ∀ i, 1 ≤ i → i < n → ν (i + 1) ≤ ν i) (hv : ∀ i, i ≤ n → v i ≤ P) :
    ∑ i ∈ Finset.range n, ν (i + 1) * (v (i + 1) - v i) ≤
      ν n * v n - ν 1 * v 0 + P * (ν 1 - ν n) := by
  induction n, hn using Nat.le_induction with
  | base => simp; linarith
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i h h' => hν i h (by omega)) (fun i h => hv i (by omega))
    have h2 := hν n hn (by omega)
    have h3 := hv n (by omega)
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem lmuNum_nonneg : ∀ (T : Type) [Fintype T] (p j q : ℕ) (μ w l : T → ℕ → ℝ) (P e : ℝ), 2 < p → 1 ≤ j → 1 ≤ q → GapCond p j q μ → (∀ τ, w τ 0 = 0) → (∀ τ, l τ 0 = 0) → (∀ τ i, i ≤ j → w τ i ≤ P) → (∀ τ i, i ≤ q → l τ i ≤ P) → (∀ τ, w τ j = l τ q) → e = -2 * ∑ τ, w τ j → ((p : ℝ) - 2) * P ≤ e → 0 ≤ e → 0 ≤ lmuNum j q μ w l := by
  intro T _ p j q μ w l P e hp hj hq hgap hw0 hl0 hw hl hwl he hPe he0
  obtain ⟨hdom, M, g, hM, hg, hpg⟩ := hgap
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ₀⟩⟩
  · simp [lmuNum]
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hP : 0 ≤ P := by have := hw τ₀ 0 (by omega); rwa [hw0] at this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM τ₀ 1 le_rfl (by omega))
  have hf : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hfM : 0 ≤ (Fintype.card T : ℝ) * M := mul_nonneg hf hM0
  have hg0 : 0 ≤ g := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' (neg_pos.2 h)]
  have key : ∀ τ, (∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
      ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) ≤
      g * w τ j + 2 * M * P := by
    intro τ
    have hA := abel_bound (μ τ) (w τ) P j hj (fun i h h' => hdom τ i h (by omega)) (hw τ)
    have hB := abel_bound (fun i => μ τ (j + i)) (fun m => l τ (q - m)) P q hq
      (fun i h h' => hdom τ (j + i) (by omega) (by omega)) (fun i _ => hl τ _ (by omega))
    simp only [Nat.sub_self, Nat.sub_zero, hl0, ← hwl τ] at hB
    rw [hw0] at hA
    have e1 : ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) =
        ∑ m ∈ Finset.range q, μ τ (j + (m + 1)) * (l τ (q - (m + 1)) - l τ (q - m)) := rfl
    rw [e1]
    have h1 := abs_le.1 (hM τ 1 le_rfl (by omega))
    have h2 := abs_le.1 (hM τ (j + q) (by omega) le_rfl)
    have h3 := mul_nonneg (sub_nonneg.2 (hg τ)) (sub_nonneg.2 (hw τ j le_rfl))
    have h4 : 0 ≤ P * (2 * M - (μ τ 1 - μ τ (j + q))) := mul_nonneg hP (by linarith [h1.2, h2.1])
    have h5 := mul_nonneg hg0 hP
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun τ _ => key τ)
  rw [Finset.sum_add_distrib (f := fun τ => g * w τ j), ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hS : ∑ τ, w τ j = -e / 2 := by linarith
  rw [hS] at hsum
  have hfin : g * (-e / 2) + (Fintype.card T : ℝ) * (2 * M * P) ≤ 0 := by
    have a1 := mul_le_mul_of_nonneg_left hPe hfM
    have a2 := mul_le_mul_of_nonneg_right hpg he0
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' h]
  unfold lmuNum
  linarith

end GlobalTheory.CompanionTheory.Ar.Crv.Chain
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBound

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg

theorem dot_bijective (K : Type) [Field K] (d : ℕ) :
    Function.Bijective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
  have hi : Function.Injective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    funext r
    have := LinearMap.congr_fun hx (Pi.single r 1)
    simpa [dotProductBilin_apply_apply] using this
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    simp [Subspace.dual_finrank_eq])).1 hi

noncomputable def endAct {K : Type} [Field K] {O : Type} [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Module.End K (Fin d → K) where
  toFun a := Matrix.toLin' (ρ a)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' a b := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  map_zero' := by simp
  map_add' a b := by simp

theorem isHom_lie {K : Type} [Field K] {C : ACurve K} {p : ℕ} {O : Type} [CommRing O] [StarRing O]
    {d : ℕ} (D : ConjData C p O d) (a : O) : IsHom C D.lie D.lie (endAct D.ρ a) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  have h2 : (D.ρH a y).1 ∈ D.lie i :=
    (D.hodge.2.2.2.2 i _).2 ⟨_, D.ρH_hom a i y hy, rfl⟩
  rw [D.ρH_fst] at h2
  simpa [endAct] using h2

theorem lmuNum_nonneg_of_conjData : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  intro K _ C p _ _ O k S T _ _ _ _ _ _ χ d D ι κ j q μ W L hp hs hc hbij hconj hj hq hW0 hL0 hWj hLq hgap
  classical
  obtain ⟨hbot, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  obtain ⟨he0, hC2⟩ := GlobalTheory.T.lie_sub_degree_bound_by_dual K C p O d D hp
  have hsplit : deg C D.lie = ∑ s, subDeg C D.lie
      (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) :=
    GlobalTheory.T.degree_sum_eigen_sub_degrees K C (Fin d → K) D.lie O k S χ hs hc (endAct D.ρ) D.lie_bun (isHom_lie D)
  have hdual : deg C (dotDual C D.lie) = - deg C D.lie :=
    (GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C (Fin d → K) (Fin d → K) D.lie (dotProductBilin K K)
      D.lie_bun (dot_bijective K d)).2.1
  have hC1 : ∀ τ, subDeg C D.lie (W τ j) = subDeg C D.lie (L τ q) := by
    intro τ
    rw [hWj, hLq]
    exact GlobalTheory.T.conjugate_eigen_sub_degree_eq K C p O k S χ d D hs hc (ι τ) (κ τ) (hconj τ)
  have hsum : deg C D.lie = 2 * ∑ τ, subDeg C D.lie (W τ j) := by
    rw [hsplit, ← (Equiv.ofBijective _ hbij).sum_comp, Fintype.sum_sum_type, two_mul]
    simp only [Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by rw [hWj]
    · exact Finset.sum_congr rfl fun τ _ => by rw [hC1, hLq]
  refine GlobalTheory.CompanionTheory.Ar.Crv.Chain.lmuNum_nonneg T p j q μ _ _ (subDeg C D.lie W₀ : ℝ)
    (deg C (dotDual C D.lie) : ℝ) hp hj hq hgap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro τ; simp [hW0, hbot]
  · intro τ; simp [hL0, hbot]
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ; exact_mod_cast hC1 τ
  · rw [hdual, hsum]; push_cast; ring
  · exact_mod_cast hC2 W₀
  · exact_mod_cast he0

end GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBoundStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.eigen_flag_slope_bound : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData | exact GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2CurveEstablished

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem subDeg_map {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {d : ℕ} (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup (Fin d → K))
    (e : V ≃ₗ[K] (Fin d → K)) (hL' : IsBun C L') (h : ∀ i v, v ∈ L i ↔ e v ∈ L' i)
    (U : Submodule K V) :
    subDeg C L' (U.map (e : V →ₗ[K] (Fin d → K))) = subDeg C L U := by
  have hb := (GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C (Fin d → K) L' (U.map (e : V →ₗ[K] (Fin d → K))) hL').1
  refine (GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C _ _ (sub C L' (U.map (e : V →ₗ[K] (Fin d → K)))) (sub C L U)
    (e.submoduleMap U).symm hb ?_).2.symm
  intro i x
  have hx : e ((e.submoduleMap U).symm x : V) = x := by
    have := (e.submoduleMap U).apply_symm_apply x
    exact congrArg Subtype.val this
  simp only [sub, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
  rw [h i, hx]

theorem mem_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    (r : O →+* Module.End K V) (σ : O →+* K) (v : V) :
    v ∈ eigSp r σ ↔ ∀ a, r a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem mem_eig {K V O : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ : O → K) (v : V) :
    v ∈ eig ρ χ ↔ ∀ a, ρ a v = χ a • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem map_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] {d : ℕ}
    (r : O →+* Module.End K V) (ρ : O →+* Matrix (Fin d) (Fin d) K) (σ : O →+* K)
    (e : V ≃ₗ[K] (Fin d → K)) (h : ∀ a v, e (r a v) = (ρ a).mulVec (e v)) :
    (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) = eig (fun a => Matrix.toLin' (ρ a)) (fun a => σ a) := by
  ext y
  obtain ⟨v, rfl⟩ := e.surjective y
  have h1 : e v ∈ (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) ↔ v ∈ eigSp r σ := by
    constructor
    · rintro ⟨u, hu, huv⟩
      have : u = v := e.injective huv
      exact this ▸ hu
    · exact fun hv => ⟨v, hv, rfl⟩
  rw [h1, mem_eigSp, mem_eig]
  refine forall_congr' fun a => ?_
  rw [Matrix.toLin'_apply, ← h, ← map_smul]
  exact e.injective.eq_iff.symm

theorem m2Curve_holds : CurveSemiAbelianConjecture := by
  intro E _ _ _ H X0 t hpow k K _ _ _ p _ _ hp C z Y hne hk hfib V _ _ _ M r hact T _ χ hsplit hχ
    j q w W L hj hq hW0 hL0 hWj hLq hgap
  letI := H.starRing
  obtain ⟨d, D, e, hlie, her⟩ := GlobalTheory.T.curve_lie_eigen_degree E H (fun _ => rfl) X0 t hpow K p C z Y hne hfib V M r hact
  let f : V →ₗ[K] (Fin d → K) := e
  have key := GlobalTheory.T.eigen_flag_slope_bound K C p (𝓞 E) k (T ⊕ T) T χ d D Sum.inl Sum.inr j q w
    (fun τ i => (W τ i).map f) (fun τ i => (L τ i).map f) hp hsplit hk
    (by
      have : (Sum.elim Sum.inl Sum.inr : T ⊕ T → T ⊕ T) = id := by ext (x | x) <;> rfl
      rw [this]; exact Function.bijective_id)
    (fun τ a => hχ τ a) hj hq
    (fun τ => by simp [hW0 τ]) (fun τ => by simp [hL0 τ])
    (fun τ => by rw [hWj τ]; exact map_eigSp r D.ρ _ e her)
    (fun τ => by rw [hLq τ]; exact map_eigSp r D.ρ _ e her) hgap
  simpa only [subDeg_map C (Y.lieLat M) D.lie e D.lie_bun hlie, f] using key

end GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2CurveEstablishedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curveSemiAbelianConjecture : CurveSemiAbelianConjecture := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds <;> assumption)
end
end
