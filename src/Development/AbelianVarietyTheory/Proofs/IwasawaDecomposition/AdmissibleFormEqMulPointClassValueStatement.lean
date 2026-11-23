module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpanStatement
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopi

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

theorem ren_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    ren τ (rel k) = GlobalTheory.PointChern.relPoly τ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ren, rel, GlobalTheory.PointChern.relPoly, map_sum, renVar]

theorem admissibleChernForm_kills_grassmannianRelationCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ →
    ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q →
    ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  intro E _ _ _ H Dw Θ hA τ j hj
  obtain ⟨h1, h2, h3, -⟩ := hA
  unfold J at hj
  induction hj using Submodule.span_induction with
  | mem x hx =>
    intro r
    rcases hx with ⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [ren_rel, mul_comm]; exact h1 τ k hk r
    · rw [mul_comm]
      simp only [ren, map_sub, rename_X, map_one]
      exact h2 _ r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
      exact h3 _ _ (by simp only [renVar, if_true]; omega) r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult (conjEmb τ.1) = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)
      exact h3 _ _ (by simp only [renVar]; simp only [Bool.false_eq_true, if_false]; omega) r
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [map_add (f := _), mul_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => intro r; rw [smul_eq_mul, map_mul (ren τ) a x, ← mul_assoc]; exact hx _

end GlobalTheory.GrassTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopiStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ → ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q → ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  first | exact @GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | exact GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | (intros; apply GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTopProd

theorem wt_add {ι : Type} (a b : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (a + b) = GlobalTheory.GrassTop.wt a + GlobalTheory.GrassTop.wt b := by
  unfold GlobalTheory.GrassTop.wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem wt_sum {ι κ : Type} (s : Finset κ) (d : κ → ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (∑ k ∈ s, d k) = ∑ k ∈ s, GlobalTheory.GrassTop.wt (d k) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.GrassTop.wt]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wt_add, ih]

theorem wt_mapDomain {ι κ : Type} (f : ι × ℕ → κ × ℕ) (hf : ∀ x, (f x).2 = x.2) (d : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (d.mapDomain f) = GlobalTheory.GrassTop.wt d := by
  unfold GlobalTheory.GrassTop.wt
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp [hf]

theorem adm_apply_prod_ren_eq_ite_mul_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) →
    ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then
      (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw g hg Θ hΘ
  have hm : ∀ τ : GlobalTheory.AllWt.Psi H, Dw.mult τ.1 = Dw.p := fun τ => GlobalTheory.PointChern.mult_of_mem Dw τ.2
  split_ifs with hall
  · have h1 : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) = ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hall τ, map_pow]
      simp [GlobalTheory.GrassTop.ren, GlobalTheory.GrassTop.renVar]
    have h2 : GlobalTheory.LieBase.pointPoly H Dw = C ((-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      unfold GlobalTheory.LieBase.pointPoly
      rw [Finset.prod_congr rfl (fun τ _ => by rw [hm τ])]
      rw [show Dw.p + Dw.q - Dw.p = Dw.q by omega]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← C_pow, ← pow_mul]
    rw [h1, h2, ← smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul, ← mul_assoc, ← mul_pow]
    norm_num
  · push_neg at hall
    obtain ⟨σ, hσ⟩ := hall
    have key : ∀ τ, ∃ d : Bool × ℕ →₀ ℕ, GlobalTheory.GrassTop.wt d ≤ Dw.p * Dw.q ∧
        (g τ ≠ X (true, Dw.p) ^ Dw.q → GlobalTheory.GrassTop.wt d < Dw.p * Dw.q) ∧ g τ = monomial d 1 := by
      intro τ
      rcases hg τ with ⟨d, hd, he⟩ | he
      · exact ⟨d, hd.le, fun _ => hd, he⟩
      · refine ⟨Finsupp.single (true, Dw.p) Dw.q, ?_, fun h => absurd he h, ?_⟩
        · simp [GlobalTheory.GrassTop.wt, Finsupp.sum_single_index, mul_comm]
        · rw [he, X_pow_eq_monomial]
    choose d hd1 hd2 hd3 using key
    have hprod : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) =
        monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1 := by
      rw [monomial_sum_one]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hd3 τ, GlobalTheory.GrassTop.ren, rename_monomial]
    have hw : GlobalTheory.GrassTop.wt (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) <
        Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
      rw [wt_sum]
      calc ∑ τ, GlobalTheory.GrassTop.wt ((d τ).mapDomain (GlobalTheory.GrassTop.renVar τ))
          = ∑ τ, GlobalTheory.GrassTop.wt (d τ) :=
            Finset.sum_congr rfl fun τ _ => wt_mapDomain (GlobalTheory.GrassTop.renVar τ) (fun _ => rfl) (d τ)
        _ < ∑ _τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q :=
            Finset.sum_lt_sum (fun τ _ => hd1 τ) ⟨σ, Finset.mem_univ _, hd2 σ hσ⟩
        _ = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by simp
    have h0 : Θ (monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1) = 0 :=
      hΘ.2.2.2 (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) hw.ne
    rw [hprod, h0, zero_mul]

end GlobalTheory.GrassTopProd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopiesStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValue

section

@[expose] public section

noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def S (H : Host E) (Dw : Datum H) : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) where
  carrier := {P | ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw)}
  zero_mem' := ⟨0, fun Θ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    exact ⟨β + β', fun Θ h => by rw [map_add (f := _), hβ Θ h, hβ' Θ h]; ring⟩
  smul_mem' := by
    rintro c a ⟨β, hβ⟩
    exact ⟨c * β, fun Θ h => by rw [map_smul, hβ Θ h, smul_eq_mul]; ring⟩

theorem prod_update {H : Host E} (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ) (σ : GlobalTheory.AllWt.Psi H)
    (h : MvPolynomial (Bool × ℕ) ℝ) :
    ∏ τ, ren τ (Function.update g σ h τ) = ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem prod_ren_mem (H : Host E) (Dw : Datum H) (s : Finset (GlobalTheory.AllWt.Psi H)) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, (∀ τ ∉ s, g τ ∈ basis Dw.p Dw.q) →
      ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨_, GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩
  | insert σ s hσ ih =>
    intro g hg
    have key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q),
        ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw := by
      intro h hh
      obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
      rw [map_add (f := _), add_mul]
      refine add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_
      · rw [zero_mul, mul_comm]
        exact GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J E H Dw Θ hΘ σ j hj _
      · clear hh
        induction hb using Submodule.span_induction with
        | mem b hb =>
          rw [← prod_update]
          refine ih _ fun τ hτ => ?_
          by_cases e : τ = σ
          · subst e; rw [Function.update_self]; exact hb
          · rw [Function.update_of_ne e]; exact hg τ (by simp [e, hτ])
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    have := key (g σ) (GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan _ _ _)
    rwa [← prod_update, Function.update_eq_self] at this

theorem var_eq {H : Host E} (x : (E →+* ℂ) × ℕ) : ∃ σ : GlobalTheory.AllWt.Psi H, ∃ y, x = renVar σ y := by
  by_cases h : x.1 (H.rt : E) = H.rt0
  · exact ⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩
  · refine ⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩
    simp [renVar, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem mul_prod_ren_mem (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, P * ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro g
    rw [C_mul']
    exact Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))
  | add a b ha hb => intro g; rw [add_mul]; exact add_mem (ha g) (hb g)
  | mul_X P x ih =>
    intro g
    obtain ⟨σ, y, rfl⟩ := var_eq (H := H) x
    have e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ) := by
      rw [prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]
      ring
    rw [mul_assoc, e]
    exact ih _

end GlobalTheory.GrassTop

theorem GlobalTheory.GrassTop.span_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ,
      GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw P
  have := GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)
  simp only [map_one, Finset.prod_const_one, mul_one] at this
  exact this
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValueStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.admissible_form_eq_mul_point_class_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTop.span_point | exact GlobalTheory.GrassTop.span_point | (intros; apply GlobalTheory.GrassTop.span_point <;> assumption)
end
end
