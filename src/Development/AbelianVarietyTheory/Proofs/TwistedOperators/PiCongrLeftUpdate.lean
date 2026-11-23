module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates

namespace Formalism.L2.SG.EvalTOntoRep

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def IsContRep (f : L2X X) (φ : X.B.I.GA → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y) ∧ ((f : X.B.I.GA → ℂ) =ᵐ[muX X] φ)

theorem eq_zero_of_ae (ψ : X.B.I.GA → ℂ) (hc : Continuous ψ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, ψ (γ * y) = ψ y)
    (h0 : ψ =ᵐ[muX X] 0) : ψ = 0 := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Count.muA_isHaar X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  set N : Set X.B.I.GA := {y | ψ y ≠ 0} with hNd
  have hN : IsOpen N := isOpen_ne_fun hc continuous_const
  have hfm : MeasurableSet X.B.fund := X.B.fund_spec.1
  have h1 : X.B.I.muA X.B.μf (N ∩ X.B.fund) = 0 := by
    have h0' : ∀ᵐ y ∂(X.B.I.muA X.B.μf), y ∈ X.B.fund → ψ y = 0 := by
      rw [← ae_restrict_iff' hfm]
      exact h0
    rw [ae_iff] at h0'
    refine measure_mono_null (fun y hy => ?_) h0'
    simp only [Set.mem_setOf_eq, Classical.not_imp]
    exact ⟨hy.2, hy.1⟩
  have hsub : N ⊆ ⋃ γ : rr_GF X.B.I, (fun y => (γ : X.B.I.GA) * y) ⁻¹' (N ∩ X.B.fund) := by
    intro y hy
    obtain ⟨γ, hγ, hγy⟩ := X.B.fund_spec.2.1 y
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
    refine ⟨?_, hγy⟩
    show ψ (γ * y) ≠ 0
    rw [hinv γ hγ y]
    exact hy
  have h2 : X.B.I.muA X.B.μf N = 0 := by
    refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
    rw [measure_preimage_mul]
    exact h1
  have h3 : N = ∅ := (hN.measure_eq_zero_iff (X.B.I.muA X.B.μf)).1 h2
  funext y
  by_contra hne
  have : y ∈ N := hne
  rw [h3] at this
  exact this

theorem contRep_unique {f : L2X X} {φ φ' : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X f φ') : φ = φ' := by
  have e := eq_zero_of_ae X (fun y => φ y - φ' y) (h.1.sub h'.1)
    (fun γ hγ y => by simp only [h.2.1 γ hγ y, h'.2.1 γ hγ y])
    ((h.2.2.symm.trans h'.2.2).mono fun y hy => by simp [hy])
  funext y
  exact sub_eq_zero.1 (congrFun e y)

theorem contRep_add {f g : L2X X} {φ ψ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X g ψ) :
    IsContRep X (f + g) (φ + ψ) :=
  ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y],
    (Lp.coeFn_add f g).trans (h.2.2.add h'.2.2)⟩

theorem contRep_smul (a : ℂ) {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) :
    IsContRep X (a • f) (a • φ) :=
  ⟨h.1.const_smul a, fun γ hγ y => by simp [h.2.1 γ hγ y], (Lp.coeFn_smul a f).trans (h.2.2.const_smul a)⟩

theorem contRep_zero : IsContRep X 0 0 :=
  ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero ℂ 2 (muX X)⟩

theorem contRep_reg {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (y : X.B.I.GA) :
    IsContRep X (X.B.R y f) (fun x => φ (x * y)) := by
  have hm : MemLp φ 2 (muX X) := (Lp.memLp f).ae_eq h.2.2
  have ef : f = hm.toLp φ := Lp.ext (h.2.2.trans hm.coeFn_toLp.symm)
  refine ⟨h.1.comp (continuous_mul_const y), fun γ hγ x => by simp only [mul_assoc, h.2.1 γ hγ], ?_⟩
  rw [ef]
  exact Formalism.L2.SG.EvalTReg.reg_toLp_X X φ h.2.1 hm y

end Formalism.L2.SG.EvalTOntoRep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
  Formalism.L2.SG.EvalTOntoRep MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def contSub : Submodule ℂ (L2X X) where
  carrier := {f | ∃ φ, IsContRep X f φ}
  add_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ + ψ, contRep_add X hφ hψ⟩
  zero_mem' := ⟨0, contRep_zero X⟩
  smul_mem' := fun a _ ⟨φ, hφ⟩ => ⟨a • φ, contRep_smul X a hφ⟩

def repOn : contSub X →ₗ[ℂ] (X.B.I.GA → ℂ) where
  toFun f := f.2.choose
  map_add' f g := contRep_unique X (f + g).2.choose_spec (contRep_add X f.2.choose_spec g.2.choose_spec)
  map_smul' a f := contRep_unique X (a • f).2.choose_spec (contRep_smul X a f.2.choose_spec)

def contRepL : L2X X →ₗ[ℂ] (X.B.I.GA → ℂ) := (LinearMap.exists_extend (repOn X)).choose

theorem contRepL_spec {f : L2X X} {φ : X.B.I.GA → ℂ} (hf : IsContRep X f φ) : contRepL X f = φ := by
  have e := LinearMap.congr_fun (LinearMap.exists_extend (repOn X)).choose_spec ⟨f, φ, hf⟩
  have e' : contRepL X f = repOn X ⟨f, φ, hf⟩ := e
  rw [e']
  exact contRep_unique X (Exists.choose_spec (p := fun φ => IsContRep X f φ) _) hf

theorem eq_of_inner_tens {p q : X.B.Hs} (h : ∀ y, ⟪p, X.B.tens y⟫_ℂ = ⟪q, X.B.tens y⟫_ℂ) : p = q := by
  let f : X.B.Hs →L[ℂ] ℂ := innerSL ℂ (p - q)
  have hsp : (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} := by
    refine (Submodule.span_le (p := LinearMap.ker (f : X.B.Hs →ₗ[ℂ] ℂ))).2 ?_
    rintro _ ⟨y, rfl⟩
    show ⟪p - q, X.B.tens y⟫_ℂ = 0
    rw [inner_sub_left, h y, sub_self]
  have hcl : closure (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} :=
    closure_minimal hsp (isClosed_eq f.continuous continuous_const)
  rw [X.B.tens_spec.2.2.closure_eq] at hcl
  have h0 : f (p - q) = 0 := hcl (Set.mem_univ _)
  have : ⟪p - q, p - q⟫_ℂ = 0 := h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] (x y : ∀ i, H i) (v : ι) (z : H v) :
    ∏ w, ⟪Function.update x v z w, y w⟫_ℂ = ⟪z, y v⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪x w, y w⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_add [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a b : X.B.H v) :
    X.B.tens (Function.update x v (a + b)) =
      X.B.tens (Function.update x v a) + X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_add_left, X.B.tens_spec.1, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, prod_update,
    inner_add_left, add_mul]

theorem tens_update_smul [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a : ℂ) (b : X.B.H v) :
    X.B.tens (Function.update x v (a • b)) = a • X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_smul_left, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, inner_smul_left, mul_assoc]

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecC (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (u τ : M.H τ))

theorem piCongrLeft_update {α β : Type} [DecidableEq α] [DecidableEq β] (P : β → Type) (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) (x : P (e a)) :
    Equiv.piCongrLeft P e (Function.update f a x) = Function.update (Equiv.piCongrLeft P e f) (e a) x := by
  apply (Equiv.piCongrLeft P e).symm.injective
  rw [Equiv.symm_apply_apply]
  funext a'
  rw [Equiv.piCongrLeft_symm_apply]
  by_cases ha : a' = a
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne (e.injective.ne ha), Equiv.piCongrLeft_apply_apply]

theorem vecC_update [DecidableEq D.what₂.Tau] [DecidableEq (NumberField.InfinitePlace X.B.I.F)]
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    vecC X M c (Function.update u τ w) = Function.update (vecC X M c u) (X.pl.symm τ) (c τ (w : M.H τ)) := by
  unfold vecC
  rw [← piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.sm i) => c i (s : M.H i)) u τ w τ'

theorem vecC_eq (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (g : ∀ v, X.B.H v)
    (hg : ∀ τ, c τ (u τ : M.H τ) = g (X.pl.symm τ)) : vecC X M c u = g := by
  unfold vecC
  have : (fun τ => c τ (u τ : M.H τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm g := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply, hg τ]
  rw [this, Equiv.apply_symm_apply]

def conjMap (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : MMap M where
  toFun u := fun y => star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹)))
  map_update_add' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_add, map_add (f := _), tens_update_add, Pi.add_apply, star_add]
  map_update_smul' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_smul, LinearIsometryEquiv.map_smulₛₗ, tens_update_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, star_star, RingHom.id_apply]

theorem conjMap_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (u : M.Vec) (y : GA D (D.sp.Y 0)) :
    conjMap X M c A h t u y = star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹))) := rfl

end GlobalTheory.ConjRowMult

end
end
end
