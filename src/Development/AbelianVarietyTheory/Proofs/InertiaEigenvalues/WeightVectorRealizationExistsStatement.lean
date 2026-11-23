module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther

section

@[expose] public section

namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_intMul_mem_MK {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (x : WL) (hx : x ∈ Φ.WK) :
    ∃ a : 𝓞 Ks, a ≠ 0 ∧ a • x ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.ScalarMultipleMembership.main
  | exact _root_.GlobalTheory.ScalarMultipleMembership.main
  | (apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarMultipleMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarMultipleMembership.main ..)

theorem exists_smul_mem_locBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j hball f
  have hfull := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j
  have hwk : (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (Rl.FW j).WK :=
    ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2
  obtain ⟨a, ha, hamk⟩ := exists_intMul_mem_MK (Rl.FW j) hfull.2 _ hwk
  refine ⟨(YS.fi j).eK.symm (a : T0.Q.c.F), ?_, hball _ ?_⟩
  · intro h
    apply ha
    have : ((a : T0.Q.c.F)) = 0 := by
      have := congrArg (YS.fi j).eK h
      simpa using this
    exact_mod_cast this
  · rw [(YS.fi j).mkK]
    have h1 : ((show ↥(S.A ((j : ℕ) + 1)).WK from (YS.fi j).eK.symm (a : T0.Q.c.F) • f)).1 =
        (YS.fi j).eK.symm (a : T0.Q.c.F) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := rfl
    rw [h1, ← algebraMap_smul D.what₂.LL, map_smul, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
      algebraMap_smul]
    exact hamk

end GlobalTheory.GeoTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weight_vector_realization_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  first | exact @GlobalTheory.GeoTie.exists_smul_mem_locBall | exact GlobalTheory.GeoTie.exists_smul_mem_locBall | (intros; apply GlobalTheory.GeoTie.exists_smul_mem_locBall <;> assumption)
end
end
