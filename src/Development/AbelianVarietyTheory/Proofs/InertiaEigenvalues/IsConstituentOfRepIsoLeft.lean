module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
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
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOneStatement

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ], {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧ ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  first | exact @GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | exact GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | (intros; apply GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEqStatement

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotentStatement

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
end
end

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemOrthogonal

section

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNe

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNeStatement

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  first | exact @GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | exact GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | (intros; apply GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft

section

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h

theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne

theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
end
end
end
