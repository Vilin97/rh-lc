module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSumSubValueEqSumSqZero

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseParamTaylorShift

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnPer.close_paramTaylor_shift : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) (F₀ : Fam I₀ g Λ), (0 : I → ℂ) ∈ F.V → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D) (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → (∀ i, t i = ∑ j, n j i) → ∀ (K : Charts F) (K₀ : Charts F₀) (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (Ta : Hol (K.W k) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀)) (Ta' : Hol (K.W k') →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀')), (∀ (h : Hol (K.W k)) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → (∀ (h : Hol (K.W k')) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀'), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta' h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀'))) (Ta'.toRingHom.comp (Charts.sh h)) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀))).comp Ta).toRingHom) := by
  intro I I₀ _ _ _ g D _ _ Λ _ F F₀ h0 hτ J N hN t r n hn hnn ht K K₀ l k k' k₀ k₀' h h₀ hW Ta Ta' hTa hTa'
  have htJ : ∀ i, t i ∈ J := fun i ↦ by rw [ht]; exact J.sum_mem fun j _ ↦ hn j i
  have hnil : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0 := fun s ↦ hN _ fun a ↦ htJ _
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l 0 h0
  obtain ⟨n', h1, h2, h3⟩ := GlobalTheory.PeriodFamily.taylor_sum_sub_value_eq_sum_sqZero J N hN r n hn hnn (fun (a : Fin g) z ↦ F.τ l z a)
    fun a ↦ analyticAt_pi_iff.1 hτa a
  have et : (fun i ↦ ∑ j, n j i) = t := funext fun i ↦ (ht i).symm
  rw [et] at h3
  obtain ⟨-, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hm : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k := fun p hp ↦ K.maps h _ (hW p hp)
  refine GlobalTheory.AnPer.close_of_sliceTaylor J N hN t htJ r n' h1 h2 (K.W k) (K₀.W k₀') (fun p : Tot I₀ g ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hm _ _ (fun f p hp ↦ ?_) fun f p hp ↦ ?_
  · refine (hTa' (Charts.sh h f) p hp).trans ?_
    have e : (fun z : I → ℂ ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := by fun_prop
      filter_upwards [hc.continuousAt.eventually ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
        using Charts.fn_sh h f hz
    rw [hcongr _ _ e, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (F.τ l) p.2 hτa (f.analytic _ (hm p hp))]
    simp only [h3]
  · have hp' := K₀.maps h₀ p hp
    have e : ∀ x : D ⊗[ℂ] Hol (K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀)) x) =
        Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev (F₀.shift l p) hp')) (fun _ _ ↦ Commute.all _ _) x := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul d c =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          Hol.ev_apply, Hol.fn_comap _ _ _ _ hp, AlgHom.id_apply]
    refine (e (Ta f)).trans ((hTa f _ hp').trans ?_)
    have e2 : (F₀.shift l p).2 = p.2 + F.τ l 0 := by simp only [Fam.shift, hτ]
    rw [e2, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hm p hp))]
    simp only [hconst, sub_self]
end
end
end
