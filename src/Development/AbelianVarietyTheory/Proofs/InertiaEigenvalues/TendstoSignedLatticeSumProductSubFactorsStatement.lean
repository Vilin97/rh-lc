module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProdStatement
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoProdFiniteAlgebraWithInvolutionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMulStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoBadWindowDivRhoStatement
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTerms

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

section Prod

variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem aeval_prod_fst (x : A₁ × A₂) (f : R[X]) : (aeval x f).1 = aeval x.1 f :=
  (aeval_algHom_apply (AlgHom.fst R A₁ A₂) x f).symm

theorem aeval_prod_snd (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f :=
  (aeval_algHom_apply (AlgHom.snd R A₁ A₂) x f).symm

theorem isIntegral_pair_one {r : A₁} (hr : IsIntegral R r) : IsIntegral R ((r, 1) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst, hfr, zero_mul]; rfl
  · rw [Prod.snd_mul, aeval_prod_snd (f := X - C 1)]; simp

theorem isIntegral_one_pair {r : A₂} (hr : IsIntegral R r) : IsIntegral R ((1, r) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst (f := X - C 1)]; simp
  · rw [Prod.snd_mul, aeval_prod_snd, hfr, zero_mul]; rfl

theorem isIntegral_fst {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.1 := hx.map (AlgHom.fst R A₁ A₂)

theorem isIntegral_snd {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := hx.map (AlgHom.snd R A₁ A₂)

end Prod

theorem dlt_map {ι κ A : Type} [CommMonoid A] (π : κ → A) (e : ι ↪ κ) (I : Finset ι) (f : A → ℚ) (y : A) :
    dlt π (I.map e) f y = dlt (π ∘ e) I f y := by
  unfold dlt
  symm
  refine Finset.sum_bij (fun J _ => J.map e) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => Finset.map_injective e h)
    (fun J hJ => ?_) (fun J _ => ?_)
  · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hJ))
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 hJ)
    exact ⟨u, Finset.mem_powerset.2 hu, rfl⟩
  · simp [Finset.prod_map, Finset.card_map]

theorem dlt_empty {ι A : Type} [CommMonoid A] (π : ι → A) (f : A → ℚ) (y : A) : dlt π ∅ f y = f y := by
  simp [dlt]

theorem pos_term_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p u₁ u₂
  refine ⟨fun h => ⟨fun i => ⟨fun r hr => ?_, fun m hm => ?_⟩, fun j => ⟨fun r hr => ?_, fun m hm => ?_⟩⟩, ?_⟩
  · have := (h (Sum.inl i)).1 (r, 1) (isIntegral_pair_one hr)
    have key : (LinearMap.inl K.O B₁.A B₂.A) (al K a ^ ((p ∘ Sum.inl) i + N) • (e₁ i * r)) =
        al K a ^ (p (Sum.inl i) + N) • (((e₁ i, 0) : B₁.A × B₂.A) * (r, 1)) :=
      Prod.ext rfl (by show (0 : B₂.A) = al K a ^ (p (Sum.inl i) + N) • ((0 : B₂.A) * 1); simp)
    rw [Submodule.mem_comap, key]
    exact this
  · exact isIntegral_fst ((h (Sum.inl i)).2 (m, 0) hm)
  · have := (h (Sum.inr j)).1 (1, r) (isIntegral_one_pair hr)
    exact ⟨_, this, rfl⟩
  · obtain ⟨m', hm', rfl⟩ := hm
    exact isIntegral_snd ((h (Sum.inr j)).2 m' hm')
  · have hT : ∀ (z : B₁.A × B₂.A), z ∈ M → ∀ t : B₂.A,
        Algebra.trace K.E (B₁.A × B₂.A) (((0 : B₁.A), t) * z) = Algebra.trace K.E B₂.A (t * z.2) := by
      intro z _ t
      rw [Algebra.trace_prod_apply]
      simp
    have hD : ∀ t : B₂.A, InDual (B₁.prod B₂) ((0 : B₁.A), t) M ↔ InDual B₂ t (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      intro t
      constructor
      · rintro h z ⟨z', hz', rfl⟩
        show Algebra.trace K.E B₂.A (t * z'.2) ∈ _
        rw [← hT z' hz' t]
        exact h z' hz'
      · intro h z hz
        convert h z.2 ⟨z, hz, rfl⟩ using 1
        exact hT z hz t
    have hE1 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₁, ((e₁ x, 0) : B₁.A × B₂.A)) = (∑ i ∈ S₁, e₁ i, 0)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hE2 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₂.map Function.Embedding.inr) = ((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₂, ((0, e₂ x) : B₁.A × B₂.A)) = (0, ∑ i ∈ S₂, e₂ i)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have keyM : ∀ y : B₁.A, indM (B₁.prod B₂) M (LinearMap.inl K.O B₁.A B₂.A y) =
        indM B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) y := fun y => by
      unfold indM
      classical
      exact if_congr Iff.rfl rfl rfl
    have keyD : ∀ t : B₂.A, indD (B₁.prod B₂) M (((0 : B₁.A), t) : B₁.A × B₂.A) =
        indD B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) t := fun t => by
      unfold indD
      classical
      exact if_congr (hD t) rfl rfl
    unfold term
    rw [dlt_map, dlt_map, dlt_empty, dlt_empty, hE1, hE2]
    have h0 : ∀ (B : InvAlg K) (e : ι₁ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    have h0' : ∀ (B : InvAlg K) (e : ι₂ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    rw [h0, h0', zero_mul, zero_mul]
    have hm0 : indM B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) 0 = 1 := by simp [indM]
    have hd0 : indD B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) 0 = 1 := by
      simp [indD, InDual]
    rw [hm0, hd0, mul_one, one_mul]
    congr 1
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      unfold indM
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inl) j) *
          (((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) * (u₁, u₂)) =
          LinearMap.inl K.O B₁.A B₂.A ((∏ j ∈ J, π₁ j) * (eS B₁ e₁ S₁ * u₁)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indM (B₁.prod B₂) M) this).trans (keyM _)
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inr) j) *
          (((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) * 1) = ((0 : B₁.A), (∏ j ∈ J, π₂ j) * (eS B₂ e₂ S₂ * 1)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indD (B₁.prod B₂) M) this).trans (keyD _)

end GlobalTheory.UnitLemma.Desc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTermsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.latticeTerm_prod_eq_mul_components : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.pos_term_prod | exact GlobalTheory.UnitLemma.Desc.pos_term_prod | (intros; apply GlobalTheory.UnitLemma.Desc.pos_term_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMulStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  first | exact @GlobalTheory.UnitLemma.FibSum.fibsum | exact GlobalTheory.UnitLemma.FibSum.fibsum | (intros; apply GlobalTheory.UnitLemma.FibSum.fibsum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactors

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem abs_sgnLat {K : UQ} (B : InvAlg K) (M : Submodule K.O B.A) : |B.sgnLat M| = 1 := by
  unfold InvAlg.sgnLat
  exact abs_eta _

theorem isUnit_alg {K : UQ} (B : InvAlg K) {a : K.O} (ha : a ≠ 0) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (IsUnit.mk0 _ ?_)
  intro h
  exact ha ((IsFractionRing.injective K.O K.E) (by rw [h, map_zero]))

variable {ι₁ ι₂ : Type} (S₁ : Finset ι₁) (S₂ : Finset ι₂) (L k : ℕ) (p : ι₁ ⊕ ι₂ → ℤ)

theorem win_inl (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win S₁ ∅ L k (p ∘ Sum.inl) := by
  intro i
  obtain ⟨h1, h2, h3, _⟩ := h (Sum.inl i)
  exact ⟨h1, h2, fun hi => h3 (by simpa using hi), fun hi => absurd hi (Finset.notMem_empty _)⟩

theorem win_inr (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win ∅ S₂ L k (p ∘ Sum.inr) := by
  intro j
  obtain ⟨h1, h2, _, h4⟩ := h (Sum.inr j)
  exact ⟨h1, h2, fun hj => absurd hj (Finset.notMem_empty _), fun hj => h4 (by simpa using hj)⟩

theorem win_of (h₁ : Win S₁ ∅ L k (p ∘ Sum.inl)) (h₂ : Win ∅ S₂ L k (p ∘ Sum.inr)) :
    Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
  rintro (i | j)
  · obtain ⟨a1, a2, a3, _⟩ := h₁ i
    exact ⟨a1, a2, fun hi => a3 (by simpa using hi), fun hi => by simp at hi⟩
  · obtain ⟨a1, a2, _, a4⟩ := h₂ j
    exact ⟨a1, a2, fun hj => by simp at hj, fun hj => a4 (by simpa using hj)⟩

theorem mid_inl (h : Mid (S₁.disjSum S₂) L k p) : Mid S₁ L k (p ∘ Sum.inl) :=
  fun i hi => h (Sum.inl i) (by simpa using hi)

theorem mid_inr (h : Mid (S₁.disjSum S₂) L k p) : Mid S₂ L k (p ∘ Sum.inr) :=
  fun j hj => h (Sum.inr j) (by simpa using hj)

end GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.ProdSum Polynomial Filter Topology

theorem GlobalTheory.UnitLemma.Desc.hh_prod_tendsto : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  classical
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) :=
      LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  have hsB : (B₁.prod B₂).P.Separable := hP ▸ hsep
  have hs₁ : B₁.P.Separable := hL₁.2
  have hs₂ : B₂.P.Separable := hL₂.2
  have hF := GlobalTheory.T.isUniformizerIdempotentFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF
  have hIS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hI'S : S₂.map Function.Embedding.inr ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hcov : ∀ i ∈ S₁.disjSum S₂, i ∈ S₁.map Function.Embedding.inl ∨ i ∈ S₂.map Function.Embedding.inr := by
    rintro (i | j) h <;> simp_all
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.alternatingDifference_term_window K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF _ _ hIS hI'S hcov N 1 1
    isUnit_one isUnit_one
  obtain ⟨L₁, hL₁'⟩ := GlobalTheory.T.alternatingDifference_term_window K B₁ ι₁ e₁ π₁ S₁ a hs₁ ha hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _)
    (fun i hi => Or.inl hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨L₂, hL₂'⟩ := GlobalTheory.T.alternatingDifference_term_window K B₂ ι₂ e₂ π₂ S₂ a hs₂ ha hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl
    (fun i hi => Or.inr hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℕ → Submodule K.O B₁.A → ℚ, ∀ k M,
      φ₁ k M = B₁.sgnLat M * term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : ℕ → Submodule K.O B₂.A → ℚ, ∀ k M,
      φ₂ k M = B₂.sgnLat M * term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      g k M = (B₁.prod B₂).sgnLat M * term (B₁.prod B₂)
        (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      f k M = g k M - K.eta (resultant B₁.P B₂.P) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) :=
    ⟨_, fun _ _ => rfl⟩
  have hfinB : ∀ k, {M ∈ (B₁.prod B₂).Lin | g k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ hsB hF _ _ hIS hI'S
      (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 ((isUnit_alg (B₁.prod B₂) ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hg, h, mul_zero])⟩)
  have hfin₁ : ∀ k, {M ∈ B₁.Lin | φ₁ k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B₁ ι₁ e₁ π₁ S₁ hs₁ hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _) _ _
      ((isUnit_alg B₁ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₁, h, mul_zero])⟩)
  have hfin₂ : ∀ k, {M ∈ B₂.Lin | φ₂ k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B₂ ι₂ e₂ π₂ S₂ hs₂ hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl _ _
      ((isUnit_alg B₂ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₂, h, mul_zero])⟩)
  have hsum : ∀ k, ∑ᶠ M ∈ (B₁.prod B₂).Lin, f k M =
      HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 -
      (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
        (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) := by
    intro k
    obtain ⟨hfinP, hfib⟩ := GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul K B₁ B₂ hL₁.1 hL₂.1 hsep (φ₁ k) (φ₂ k) (hfin₁ k) (hfin₂ k)
    have e1 : ∀ M, f k M = g k M + (-K.eta (resultant B₁.P B₂.P)) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) := by
      intro M; rw [hf]; ring
    rw [finsum_mem_congr rfl (fun M _ => e1 M)]
    rw [finsum_mem_add_distrib' ?_ ?_, ← mul_finsum_mem, hfib]
    · have h0 : ∑ᶠ M ∈ (B₁.prod B₂).Lin, g k M = HH (B₁.prod B₂)
          (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hg k M
      have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ k M = HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₁ k M
      have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ k M = HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₂ k M
      rw [h0, h1, h2]
      unfold UQ.eta
      rw [neg_eq_neg_one_mul (K.q : ℚ), mul_zpow]
      ring
    · exact (hfinB k).subset (fun M ⟨hM, hne⟩ => ⟨hM, hne⟩)
    · exact hfinP.subset (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by simp only [h, mul_zero])⟩)
  have hbound : ∀ k M, |f k M| ≤ 2 ^ (S₁.map (@Function.Embedding.inl ι₁ ι₂)).card * 2 ^ (S₂.map (@Function.Embedding.inr ι₁ ι₂)).card +
      2 ^ S₁.card * 2 ^ (∅ : Finset ι₁).card * (2 ^ (∅ : Finset ι₂).card * 2 ^ S₂.card) := by
    intro k M
    rw [hf, hg, hφ₁, hφ₂]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_sgnLat, one_mul]; exact abs_term _ _ _ _ _ _ _
    · rw [abs_mul, abs_eta, one_mul, abs_mul, abs_mul, abs_mul, abs_sgnLat, abs_sgnLat, one_mul, one_mul]
      exact mul_le_mul (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _) (abs_nonneg _) (by positivity)
  have hsupp : ∀ k, max L₀ (max L₁ L₂) ≤ k → ∀ M ∈ (B₁.prod B₂).Lin, ∀ p,
      Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p →
      f k M ≠ 0 → Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (max L₀ (max L₁ L₂)) k p ∧
        ¬ Mid (S₁.disjSum S₂) (max L₀ (max L₁ L₂)) k p := by
    intro k hk M hM p hp hne
    set L := max L₀ (max L₁ L₂) with hL
    have tp := GlobalTheory.T.latticeTerm_prod_eq_mul_components K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p (algebraMap K.O B₁.A a ^ (2 * k))
      (algebraMap K.O B₂.A a ^ (2 * k))
    obtain ⟨hp₁, hp₂⟩ := tp.1 hp
    have a0 := hL₀ L (le_max_left _ _) k hk M p hp
    have a1 := hL₁' L (le_trans (le_max_left _ _) (le_max_right _ _)) k hk _ _ hp₁
    have a2 := hL₂' L (le_trans (le_max_right _ _) (le_max_right _ _)) k hk _ _ hp₂
    rw [one_mul] at a0 a1 a2
    have hwin : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
      by_cases h0 : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M = 0
      · have hne' := hne
        rw [hf, hg, hφ₁, hφ₂, h0] at hne'
        have t1 : term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        have t2 : term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        exact win_of S₁ S₂ L k p (a1.1 t1) (a2.1 t2)
      · exact a0.1 h0
    refine ⟨hwin, fun hmid => hne ?_⟩
    have e0 := a0.2 hwin hmid
    have e1 := a1.2 (win_inl S₁ S₂ L k p hwin) (mid_inl S₁ S₂ L k p hmid)
    have e2 := a2.2 (win_inr S₁ S₂ L k p hwin) (mid_inr S₁ S₂ L k p hmid)
    have hA : (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) =
        ((algebraMap K.O B₁.A a ^ (2 * k), algebraMap K.O B₂.A a ^ (2 * k)) : B₁.A × B₂.A) :=
      Prod.ext (by simp) (by simp)
    have key : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M =
        term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) *
        term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      rw [e1, e2]
      refine Eq.trans e0 (Eq.trans ?_ tp.2)
      congr 2
    rw [hf, hg, hφ₁, hφ₂, key, GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul K B₁ B₂ hsep M hM]
    ring
  have hc := GlobalTheory.T.tendsto_finsum_div_rho_pow_zero K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF (S₁.map Function.Embedding.inl)
    (S₂.map Function.Embedding.inr) hcov N (max L₀ (max L₁ L₂)) _ f hN hbound hsupp
  refine hc.congr (fun k => ?_)
  rw [hsum k]
  have hA' : (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      ((algebraMap K.O B₁.A a ^ k, algebraMap K.O B₂.A a ^ k) : B₁.A × B₂.A) :=
    Prod.ext (by simp) (by simp)
  have hr : (B₁.prod B₂).rho (algebraMap K.O (B₁.prod B₂).A a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := by
    rw [← GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution K B₁ B₂]
    exact congrArg _ hA'
  rw [hr, Nat.cast_mul]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactorsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | exact GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | (intros; apply GlobalTheory.UnitLemma.Desc.hh_prod_tendsto <;> assumption)
end
end
