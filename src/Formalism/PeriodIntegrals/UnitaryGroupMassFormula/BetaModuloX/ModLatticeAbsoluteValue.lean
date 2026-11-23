module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MapEqOfIff
public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaSummable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MinkFix

section

@[expose] public section

noncomputable section

open scoped Classical

open NumberField Module

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q4

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Type} [AddCommGroup Q] [Module E Q] [Module (𝓞 E) Q] [IsScalarTower (𝓞 E) E Q]

theorem mink_fix (L : Submodule (𝓞 E) Q) (hL : L.FG) (φ : Q →ₗ[E] Q) (hφL : ∀ x ∈ L, φ x ∈ L)
    (n : ℕ) (hn : 0 < n) (hpow : ∀ x, φ^[n] x = x) (g : ℕ) (hg : 3 ≤ g)
    (hcong : ∀ x ∈ L, ∃ y ∈ L, φ x - x = g • y) : ∀ x ∈ L, φ x = x := by
  have hfinO : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have hfinZ : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : IsAddTorsionFree L :=
    Formalism.HermitianLatticesTheory.isAddTorsionFree_ringOfIntegers_submodule (K := E) L
  have : HasUniqueDiv L := IsAddTorsionFree.hasUniqueDiv
  have hfree : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ψ : L →ₗ[ℤ] L :=
    (((φ.restrictScalars (𝓞 E)).restrict hφL : L →ₗ[𝓞 E] L) : L →+ L).toIntLinearMap
  have hψ : ∀ x : L, (ψ x : Q) = φ x := fun x => rfl
  have hiter : ∀ (k : ℕ) (x : L), ((ψ^[k] x : L) : Q) = φ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hψ, ih]
  have hψn : ψ ^ n = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [pow_apply_eq_iterate, hiter, hpow]
    rfl
  have hc : ∀ x : L, ∃ y : L, ψ x - x = (g : ℤ) • y := by
    intro x
    obtain ⟨y, hy, h⟩ := hcong x x.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_sub, hψ, h, Submodule.coe_smul_of_tower, natCast_zsmul]
  choose yf hyf using hc
  let b := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ L))
  let A := LinearMap.toMatrixAlgEquiv b ψ
  let B : Matrix (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L)))
      (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ L))) ℤ :=
    Matrix.of fun i j => b.repr (yf (b j)) i
  have hAn : A ^ n = 1 := by
    show (LinearMap.toMatrixAlgEquiv b ψ) ^ n = 1
    rw [← map_pow, hψn, map_one]
  have hAB : A = 1 + (g : ℤ) • B := by
    ext i j
    show (LinearMap.toMatrixAlgEquiv b ψ) i j = _
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have h := hyf (b j)
    rw [sub_eq_iff_eq_add'] at h
    rw [h, map_add (f := _), map_zsmul, Finsupp.add_apply, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    simp [B, Matrix.one_apply, eq_comm]
  have hA1 := Formalism.HermitianLatticeCounting.P.finite_order_congruence _ n (g : ℤ) A B (by exact_mod_cast hg) hn hAn hAB
  have hψ1 : ψ = 1 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact hA1
  intro x hx
  have := congrArg (fun f : L →ₗ[ℤ] L => ((f ⟨x, hx⟩ : L) : Q)) hψ1
  simpa [hψ] using this

end Q4

end PI.UnitaryGroupMassFormula.BetaModX
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.ModLatticeAbsoluteValue

section

@[expose] public section

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section MX

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem xsp_le_orth {T' : E} (F' : LFlag S r T') : Xsp F' ≤ orth S (Xsp F') := by
  intro v hv
  rw [mem_orth']
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    induction hv using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨b, rfl⟩ := hy'
      exact F'.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  | zero => simp
  | add y y' _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h1 => simp [h1]

theorem mod_lattice_absolute_value : ModXAbs := by
  intro E _ _ _ S r T' g F' Λ γ hτ hT hg hΛ hpos hA hXγ hz hcong v hv
  have hX : ∀ w, γ w ∈ Xsp F' ↔ w ∈ Xsp F' := by
    intro w
    constructor
    · intro h
      rw [← hXγ] at h
      obtain ⟨w', hw', he⟩ := h
      rw [← γ.injective he]
      exact hw'
    · intro h
      rw [← hXγ]
      exact ⟨w, h, rfl⟩
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hA.1
  have hU := orth_iff F' γ hiso hX
  obtain ⟨n, hn, hpow⟩ := γQ_finOrd F' hT hτ hpos Λ hΛ γ hA hU hX hz
  let φ : Qt F' →ₗ[E] Qt F' := (γQ F' γ hU hX : Qt F' →ₗ[E] Qt F')
  have hφL : ∀ x ∈ Lb F' Λ, φ x ∈ Lb F' Λ := by
    intro x hx
    have h := γQ_Lb F' Λ γ hU hX hA
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hk : ∀ (k : ℕ) (x : Qt F'), φ^[k] x = (γQ F' γ hU hX ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  have hpow' : ∀ x, φ^[n] x = x := by
    intro x
    rw [hk, hpow]
    rfl
  have hgE : ((g : ℕ) : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hcongQ : ∀ x ∈ Lb F' Λ, ∃ y ∈ Lb F' Λ, φ x - x = g • y := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hx
    have hw : (a : S.V) ∈ Lrep Λ F' := ⟨ha, a.2⟩
    obtain ⟨s, hs, ξ, hξ, hsξ⟩ := Submodule.mem_sup.1 (hcong a hw)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    have hξX : ξ ∈ Xsp F' := hξ.2
    have hgl : ((g : ℕ) : E) • l = γ a - a - ξ := by
      rw [← hsξ, ← algebraMap_smul E ((g : ℕ) : 𝓞 E) l, map_natCast]
      abel
    have hlU : l ∈ Uo F' := by
      have h1 : γ a - a - ξ ∈ Uo F' :=
        sub_mem (sub_mem ((hU a).2 a.2) a.2) (xsp_le_orth F' hξX)
      have : l = ((g : ℕ) : E)⁻¹ • (γ a - a - ξ) := by
        rw [← hgl, smul_smul, inv_mul_cancel₀ hgE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    refine ⟨Submodule.Quotient.mk ⟨l, hlU⟩, (mem_Lb F' Λ).2 ⟨⟨l, hlU⟩, hl, rfl⟩, ?_⟩
    show γQ F' γ hU hX (Submodule.Quotient.mk a) - Submodule.Quotient.mk a =
      g • (Submodule.Quotient.mk ⟨l, hlU⟩ : Qt F')
    rw [γQ_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) ∈ Xsp F'
    have hco : ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = ξ := by
      have e2 : ((g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = g • l := by simp
      rw [Submodule.coe_sub, Submodule.coe_sub, e2, γU_coe]
      have e : (g • l : S.V) = ((g : ℕ) : E) • l := (Nat.cast_smul_eq_nsmul E g l).symm
      rw [e, hgl]
      abel
    rw [hco]
    exact hξX
  have hLb := Lb_lattice F' Λ hΛ
  have hfg : (Lb F' Λ).FG := by
    first | exact hLb.toIsLattice.fg | exact hLb.fg
  have hfix := mink_fix (Lb F' Λ) hfg φ hφL n hn hpow' g hg hcongQ
  have hall : ∀ q, φ q = q := by
    have hle : Submodule.span E (Lb F' Λ : Set (Qt F')) ≤
        LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') := by
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hfix x hx, sub_self]
    intro q
    have hq : q ∈ LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') :=
      hle (by
        first
        | letI : Submodule.IsFullLattice E (Lb F' Λ) := hLb
          rw [Submodule.IsFullLattice.span_eq_top]
          exact Submodule.mem_top
        | obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (Pk F') q
          obtain ⟨o, ho, hoa⟩ := Bl.general_b_fact_third''''.goal1 S Λ hΛ (a : S.V)
          have hmem : (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') ∈ Lb F' Λ :=
            (mem_Lb F' Λ).2 ⟨o • a, by simpa using hoa, rfl⟩
          have ho' : algebraMap (𝓞 E) E o ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 ho
          have ha : (Submodule.Quotient.mk (p := Pk F') a : Qt F') =
              (algebraMap (𝓞 E) E o)⁻¹ • (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') := by
            rw [Submodule.Quotient.mk_smul, ← algebraMap_smul E o, smul_smul, inv_mul_cancel₀ ho', one_smul]
          rw [ha]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hmem))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hq
    exact hq
  have h := hall (Submodule.Quotient.mk ⟨v, hv⟩)
  change Submodule.Quotient.mk (γU F' γ hU ⟨v, hv⟩) = Submodule.Quotient.mk (p := Pk F') ⟨v, hv⟩ at h
  rw [Submodule.Quotient.eq] at h
  exact h

end MX

end PI.UnitaryGroupMassFormula.BetaModX
end
end
end
