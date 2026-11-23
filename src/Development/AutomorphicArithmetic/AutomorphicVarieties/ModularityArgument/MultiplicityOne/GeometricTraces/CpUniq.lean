module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwTrConjEquiv

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem twTr_conj_equiv : ∀ (G : Type) [Group G] (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : ρ.Equiv ρ') (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V), twTr ρ' K K' f (e.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ e.toLinearEquiv.symm.toLinearMap) = twTr ρ K K' f A := by
  intro G _ V V' _ _ _ _ ρ ρ' e K K' f A
  set φ := e.toLinearEquiv with hφ
  have hint : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa [hφ] using h
  have hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v')) := fun g v' => by
    rw [hint, φ.apply_symm_apply]
  have hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K' := by
    intro v'
    show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔
      (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    refine forall_congr' fun h => ?_
    rw [hint']
    constructor
    · intro H
      exact (φ.symm_apply_eq.2 H.symm).symm
    · intro H
      rw [H, φ.apply_symm_apply]
  have hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A) := by
    have hs := (φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))
    unfold levOp
    rw [map_smul]
    congr 1
    refine Eq.trans ?_ hs.symm
    congr 1
    funext q
    ext v'
    simp [LinearEquiv.conj_apply, hint']
  have hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hA]
  have hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K' := by
    ext v'
    rw [Submodule.mem_map_equiv, hmem]
  set L := levOp ρ K K' f A with hL
  have hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K') := by
    constructor
    · intro H v hv
      have h1 : φ v ∈ fixed ρ' K' := (hmem _).2 (by simpa using hv)
      have h2 := (hmem _).1 (H _ h1)
      simpa [LinearEquiv.conj_apply] using h2
    · intro H v' hv'
      rw [hmem]
      simpa [LinearEquiv.conj_apply] using H _ ((hmem _).1 hv')
  unfold twTr
  simp only [hlev]
  by_cases h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'
  · rw [dite_eq_left (hc.2 h), dite_eq_left h]
    let ψ := φ.ofSubmodules _ _ hmap
    have hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h) := by
      ext ⟨v', hv'⟩
      simp [ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]
    rw [hr, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hc.1 h), dite_eq_right h]

end GlobalTheory.BCT
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.CpUniq

section

@[expose] public section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

private theorem trc_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (K : Subgroup G) (f : G → ℂ) :
    trc ρ K f = trc ρ' K f := by
  have hid : e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact e.toLinearEquiv.apply_symm_apply v
  have h := GlobalTheory.BCT.twTr_conj_equiv G V V' ρ ρ' e K (K ⊓ GlobalTheory.BCT.rStab f ⊓ GlobalTheory.BCT.rStab fun y => f y⁻¹) f LinearMap.id
  rw [hid] at h
  exact h.symm

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hw]
  trivial

private noncomputable def toUL (hw : IsSplitAt w) (τ : SmIrr (GLw n w)) : SmIrr (UL n w) where
  V := τ.V
  ρ := τ.ρ.comp (UL n w).subtype
  smooth v := (τ.smooth v).preimage continuous_subtype_val
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, mem_UL hw g⟩ x hx⟩

private theorem isCompU_toUL (hw : IsSplitAt w) {σ : Submodule ℂ (UA E n → ℂ)} {τ : SmIrr (GLw n w)} (h : Cp σ w τ) :
    IsCompU σ w (toUL hw τ) := by
  obtain ⟨-, F, hF0, hFσ, hF⟩ := h
  refine ⟨{ toFun := fun x => ⟨cLoc w x.1, mem_UL hw _⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl, (toUL hw τ).irred, F, hF0, hFσ, fun x v => hF x v⟩

private noncomputable def equivOfUL (hw : IsSplitAt w) {τ τ' : SmIrr (GLw n w)} (e : (toUL hw τ).ρ.Equiv (toUL hw τ').ρ) : τ.ρ.Equiv τ'.ρ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' ⟨g, mem_UL hw g⟩

end Split

theorem UpperTheory.V.Z.Mult.cpUniq :
    UpperTheory.V.Z.Mult.CpUniq := by
  intro E _ _ _ hU n hn σ hσ w hw τ τ' h h'
  obtain ⟨e⟩ := (GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn σ hσ w).2 (toUL hw τ) (toUL hw τ') (isCompU_toUL hw h) (isCompU_toUL hw h')
  have e' := equivOfUL hw e
  exact ⟨fun B hB => GlobalTheory.PrinSat.hasSatGL_of_equiv e'.symm hB, fun f => trc_of_equiv e' _ f⟩
end
end
