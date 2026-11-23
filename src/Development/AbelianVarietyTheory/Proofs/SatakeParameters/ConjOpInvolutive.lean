module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidalStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
import Mathlib.Algebra.Module.StablyFree.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctional

section

@[expose] public section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ContraPair

theorem iso_of_common_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  intro E _ _ _ a π s₁ s₂ hs₁ hs₂ B₁ B₂ hl₁ hr₁ hf₁ hc₁ hL₁ hl₂ hr₂ hf₂ hc₂ hL₂ ψ₁ ψ₂ hψ₁ hψ

  have irr : ∀ P : Submodule ℂ π.V, (∀ o, ∀ x ∈ P, π.op o x ∈ P) → P ≠ ⊥ → P = ⊤ := by
    intro P hP h0
    have hst : _root_.GlobalTheory.CuspRep.IsStable (P.map π.V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨π.op o x, hP o x hx, rfl⟩
    have e := Submodule.comap_map_eq_of_injective π.V.injective_subtype P
    rcases π.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact absurd (by rw [← e, h, Submodule.comap_bot, Submodule.ker_subtype]) h0
    · rw [← e, h, Submodule.comap_subtype_self]
  have hfin : ∀ k (φ : π.V), π.op (.fin k) (π.op (.fin k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (finRep E a k * finRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)
  have hcpt : ∀ k (φ : π.V), π.op (.cpt k) (π.op (.cpt k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (cptRep E a k * cptRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)

  have key : ∀ o ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ∀ φ, B₁ φ (π.op (s₁ o) ψ) = B₂ φ (π.op (s₂ o) ψ') := by
    intro o ψ ψ' h φ
    cases o with
    | fin k =>
      have e1 := hf₁ k (π.op (.fin k⁻¹) φ) ψ
      have e2 := hf₂ k (π.op (.fin k⁻¹) φ) ψ'
      rw [hfin] at e1 e2
      rw [e1, e2, h]
    | cpt k =>
      have e1 := hc₁ k (π.op (.cpt k⁻¹) φ) ψ
      have e2 := hc₂ k (π.op (.cpt k⁻¹) φ) ψ'
      rw [hcpt] at e1 e2
      rw [e1, e2, h]
    | lie X =>
      have e1 := hL₁ X φ ψ
      have e2 := hL₂ X φ ψ'
      have e3 := h (π.op (.lie X) φ)
      linear_combination e1 - e2 - e3
  have uniq : ∀ x y : π.V, (∀ φ, B₂ φ x = B₂ φ y) → x = y := fun x y h =>
    sub_eq_zero.1 (hr₂ _ fun φ => by rw [map_sub, h, sub_self])
  have inj₂ : Function.Injective B₂.flip := fun x y h => uniq x y fun φ => by
    simpa using LinearMap.congr_fun h φ

  let N : Submodule ℂ π.V := (LinearMap.range B₂.flip).comap B₁.flip
  have memN : ∀ ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ψ ∈ N := fun ψ ψ' h =>
    ⟨ψ', LinearMap.ext fun φ => by simpa using (h φ).symm⟩
  have hN : N = ⊤ := by
    refine irr N (fun o x hx => ?_) fun h => hψ₁ ((Submodule.eq_bot_iff _).1 h ψ₁ (memN _ _ hψ))
    obtain ⟨y, hy⟩ := hx
    have h : ∀ φ, B₁ φ x = B₂ φ y := fun φ => by simpa using (LinearMap.congr_fun hy φ).symm
    have := key (s₁ o) x y h
    rw [hs₁ o] at this
    exact memN _ _ this
  have hmem : ∀ ψ, B₁.flip ψ ∈ LinearMap.range B₂.flip := fun ψ =>
    (show ψ ∈ N from hN ▸ Submodule.mem_top)
  let T : π.V →ₗ[ℂ] π.V := (LinearEquiv.ofInjective B₂.flip inj₂).symm.toLinearMap ∘ₗ
    B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem
  have hT : ∀ ψ φ, B₂ φ (T ψ) = B₁ φ ψ := by
    intro ψ φ
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective B₂.flip inj₂).apply_symm_apply
      (B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem ψ))
    rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h1
    have h2 := LinearMap.congr_fun h1 φ
    rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
    exact h2
  have hTo : ∀ o φ, T (π.op (s₁ o) φ) = π.op (s₂ o) (T φ) := fun o φ =>
    uniq _ _ fun χ => by rw [hT]; exact key o φ (T φ) (fun χ => (hT φ χ).symm) χ
  have injT : Function.Injective T := fun x y h =>
    sub_eq_zero.1 (hr₁ _ fun φ => by rw [map_sub, ← hT, ← hT, h, sub_self])
  have hR : LinearMap.range T = ⊤ := by
    refine irr _ (fun o x hx => ?_) fun h => hψ₁ (injT ?_)
    · obtain ⟨y, rfl⟩ := hx
      refine ⟨π.op (s₁ (s₂ o)) y, ?_⟩
      rw [hTo, hs₂ o]
    · rw [map_zero]
      exact (Submodule.eq_bot_iff _).1 h _ ⟨ψ₁, rfl⟩
  exact ⟨LinearEquiv.ofBijective T ⟨injT, LinearMap.range_eq_top.1 hR⟩, hTo⟩

end GlobalTheory.ContraPair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctionalStatement

section

@[expose] public section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  first | exact @GlobalTheory.ContraPair.iso_of_common_functional | exact GlobalTheory.ContraPair.iso_of_common_functional | (intros; apply GlobalTheory.ContraPair.iso_of_common_functional <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresented

section

@[expose] public section

namespace GlobalTheory

theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresentedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by
  first | exact @GlobalTheory.functional_fixed_by_idempotent_represented | exact GlobalTheory.functional_fixed_by_idempotent_represented | (intros; apply GlobalTheory.functional_fixed_by_idempotent_represented <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConjStatement

section

@[expose] public section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive

section

@[expose] public section

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdBack

theorem invTOp_involutive {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    Function.Involutive (invTOp : Op E a → Op E a) := by
  intro o
  cases o with
  | fin k => simp only [invTOp]; congr 1
  | cpt k => simp only [invTOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X =>
    simp only [invTOp]; congr 1
    funext i j
    exact neg_neg (X i j)

theorem conjOp_involutive {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} :
    Function.Involutive (conjOp : Op L a → Op L a) := by
  intro o
  cases o with
  | fin k => simp only [conjOp]; congr 1; ext i j; simp [GlobalTheory.ThetaPull.cFin_cFin]
  | cpt k => simp only [conjOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X => simp only [conjOp]; congr 1; ext i j; simp

theorem isCsd_of_paired : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (a : ℕ) (π : CuspSub L a), Paired π π invTOp → DualIsConj π → π.IsCsd := by
  intro hP L _ _ _ a π h1 h2
  obtain ⟨B₁, l1, r1, f1, c1, x1⟩ := h1
  obtain ⟨B₂, l2, r2, f2, c2, x2⟩ := h2
  obtain ⟨P, hP0, hPP, hfin, hadj⟩ := GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal hP L a π
  obtain ⟨P₁, e1⟩ := hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1
  obtain ⟨P₂, e2⟩ := hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (LinearMap.ext h)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)
  have hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P := by rw [LinearMap.comp_assoc, hPP]
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf
  have hne : ψ₁ ≠ 0 := by
    rintro rfl
    apply hg
    have := hψ₁ v
    simp only [map_zero, LinearMap.comp_apply] at this
    exact this.symm
  obtain ⟨S, hS⟩ := GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1
    l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)
  exact GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS

end GlobalTheory.CsdBack

end
end
end
