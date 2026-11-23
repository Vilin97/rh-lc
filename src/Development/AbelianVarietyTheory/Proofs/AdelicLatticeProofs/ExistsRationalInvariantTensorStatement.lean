module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HilbertFinitenessLeftInvariantMatrixPolyStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTransposeStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducibleStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyCompletelyReducibleStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormPropertiesStatement
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantFormEqSumInvariantTensors

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem invariant_form_eq_sum_invariant_tensors : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  intro ι _ _ Γ hP hS n F hF hhom
  obtain ⟨-, hinv, -, hp⟩ := GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι
  obtain ⟨p, hpev, hpl, hpsurj⟩ := hp n
  obtain ⟨l, hl⟩ := hpsurj F hhom
  obtain ⟨R₁, h1a, -, -, h1d, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' ((Fin n → ι) → ℂ)
    ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hP hS n U (by
        rintro _ ⟨g, hg, rfl⟩ v hv
        simpa [Matrix.toLin'_apply] using hU _ ⟨g, hg, rfl⟩ v hv)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      simpa [Matrix.toLin'_apply] using hU' _ ⟨g, hg, rfl⟩ v hv)
  obtain ⟨R₂, -, h2b, h2c, -, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hP hS U (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      exact hU' g hg v hv)
  have hfix : ∀ v, ∀ g ∈ Γ, R₁ v ᵥ* tpow n g = R₁ v := by
    intro v g hg
    have := h1a v _ ⟨g, hg, rfl⟩
    simpa [Matrix.toLin'_apply, Matrix.mulVec_transpose] using this
  have hkill : ∀ b, ∀ x ∈ Submodule.span ℂ
      {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}, R₂ (p b x) = 0 := by
    intro b x hx
    have hle : Submodule.span ℂ
        {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}
        ≤ LinearMap.ker (R₂ ∘ₗ p b) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, w, rfl⟩
      have h := h2c (p b w) _ ⟨g, hg, rfl⟩
      simp only [AlgHom.toLinearMap_apply, hpl] at h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, map_sub,
        Matrix.toLin'_apply, Matrix.mulVec_transpose, h, sub_self]
    exact hle hx
  have hb : ∀ b v, R₂ (p b v) = p b (R₁ v) := by
    intro b v
    have h0 := hkill b _ (h1d v)
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [h0]
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    simp only [AlgHom.toLinearMap_apply, hpl, hfix v g hg]
  have hRF : R₂ F = F := by
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    exact (hinv Γ F).1 hF g hg
  have hF' : F = ∑ b, p b (R₁ (l b)) := by

    rw [← hRF, hl, map_sum]
    exact Finset.sum_congr rfl fun b _ => hb b _
  refine ⟨fun b => R₁ (l b), fun b g hg => hfix _ g hg, fun y => ?_⟩
  rw [hF']
  simp only [← hpev]
  unfold evC

  rw [map_sum]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantFormEqSumInvariantTensorsStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  first | exact @GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | exact GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors | (intros; apply GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRationalKroneckerInvariants

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]

    simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRationalKroneckerInvariantsStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_span_rational_kroneckerInvariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  first | exact @GlobalTheory.ClassFin.RationalInvariants.mem_span_rational | exact GlobalTheory.ClassFin.RationalInvariants.mem_span_rational | (intros; apply GlobalTheory.ClassFin.RationalInvariants.mem_span_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensor

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add (f := _), ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensorStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_invariant_tensor' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  first | exact @GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor | exact GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor | (intros; apply GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor <;> assumption)
end
end
