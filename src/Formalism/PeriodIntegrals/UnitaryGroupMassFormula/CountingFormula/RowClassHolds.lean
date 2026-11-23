module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HermFormShiftedVectorZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LisoSmulMem
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowUnitCondition

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (o : 𝓞 K) :
    ∃ o' : 𝓞 K, (o' : K) = star (o : K) := by
  have h1 : IsIntegral ℤ (star (o : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (o : K), h1⟩, rfl⟩

theorem exists_one {K : Type} [Field K] [NumberField K] [StarRing K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h : W →ₗ⋆[K] W →ₗ[K] K) (M : Submodule (𝓞 K) W)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h M) {z : W} (hz : z ∈ M)
    (hprim : ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) : ∃ m ∈ M, h m z = 1 := by
  classical

  have memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x := by
    intro x
    conv_lhs => rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]

  let I : Ideal (𝓞 K) :=
    { carrier := {o | ∃ m ∈ M, h m z = star (o : K)}
      add_mem' := by
        rintro a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
        refine ⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, e₁, e₂]
        show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a + b))
        rw [map_add (f := _), star_add]
      zero_mem' := ⟨0, M.zero_mem, by
        rw [map_zero, LinearMap.zero_apply]
        show (0 : K) = star (algebraMap (𝓞 K) K 0)
        rw [map_zero, star_zero]⟩
      smul_mem' := by
        rintro a b ⟨m, hm, e⟩
        refine ⟨a • m, M.smul_mem a hm, ?_⟩
        have ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m := (algebraMap_smul K a m).symm
        rw [ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]
        simp only [smul_eq_mul, starRingEnd_apply]
        show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a * b))
        rw [map_mul, star_mul'] }
  have memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K) := fun o => Iff.rfl
  by_contra hne
  push_neg at hne
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (memI 1).1 h1
    exact hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)
  obtain ⟨c, hc, hc1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top
  have hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hPne] at hc

  have hcz : (star c) • z ∈ M := by
    rw [memM]
    intro m hm
    obtain ⟨t, ht⟩ := (memM z).1 hz m hm
    obtain ⟨t', ht'⟩ := star_int t
    have e1 : h m z = star (t' : K) := by rw [ht', star_star]; exact ht.symm
    have ht'I : t' ∈ I := (memI t').2 ⟨m, hm, e1⟩
    have hcy := hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at hcy
    obtain ⟨s, hs⟩ := hcy
    obtain ⟨s', hs'⟩ := star_int s
    refine ⟨s', ?_⟩
    rw [map_smul, smul_eq_mul, e1, ← star_mul']
    change (s' : K) = _
    rw [hs']
    congr 1
  obtain ⟨o, ho⟩ := hprim _ hcz
  obtain ⟨o', ho'⟩ := star_int o
  apply hc1
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_unit_condition : RowZUnit := by
  intro D u F0 Λ hrow
  obtain ⟨_, hMU, hzM, hprim⟩ := row_lattice_mass_holds D u F0 Λ hrow
  obtain ⟨m, hm, hm1⟩ := exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim
  obtain ⟨a, haΛ, rfl⟩ := (RowMPf.mem_Mof D F0 Λ m).1 hm
  refine ⟨a, haΛ, a.2, ?_⟩
  rw [zbar, hWb_mk] at hm1
  exact hm1

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_unit_condition : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnit := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TraceOneUnramified

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trace_one_unramified : TraceOne := fun D =>
  Formalism.MainNotions.BridgeLemma.l_theta D.host.E D.sp.cm.cmUnram

section Dual

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem exists_dual0 : ∃ g0 : Fin D.R.rS → (VS D).V, IsDual0 F0 g0 := by
  let Φ : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) := LinearMap.pi (fun a => (VS D).hT (F0.e a))
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set μ : Fin D.R.rS → D.host.E := fun a => f (fun j => if a = j then 1 else 0) with hμdef
    have hv : ∀ v, ∑ a, (VS D).hT (F0.e a) v * μ a = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hle (LinearMap.mem_range_self Φ v)
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ, LinearMap.pi_apply, smul_eq_mul, μ] using h1
    have hx : ∑ a, star (μ a) • F0.e a = 0 := by
      apply (VS D).nondeg.1
      intro v

      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      rw [← hv v]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hμ : ∀ a, μ a = 0 := by
      intro a
      have := Fintype.linearIndependent_iff.1 F0.e_indep (fun a => star (μ a)) hx a
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    have : f (fun j => if a = j then 1 else 0) = 0 := hμ a
    rw [this, smul_zero]
  refine ⟨fun b => Classical.choose (LinearMap.range_eq_top.1 hsurj (Pi.single b 1)), ?_⟩
  intro a b
  have h := Classical.choose_spec (LinearMap.range_eq_top.1 hsurj (Pi.single b 1))
  have h2 := congrFun h a
  simp only [Φ, LinearMap.pi_apply] at h2
  rw [h2, Pi.single_apply]

end Dual

theorem row_dual_frame : RowDualFrame := by
  intro D u F0 Λ hΛ
  obtain ⟨g0, hg0⟩ := exists_dual0 F0
  have hlat : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hiso : ∀ x ∈ F0.X, ∀ y ∈ F0.X, (VS D).hT x y = 0 := fun x hx y hy => hX_X F0 hx hy
  obtain ⟨P, P', hadj, hid, hX, _, hint', _⟩ :=
    Formalism.MainNotions.BridgeLemma.l_iso Formalism.MainNotions.BridgeLemma.l_adj Formalism.MainNotions.BridgeLemma.l_retr Formalism.MainNotions.BridgeLemma.l_theta
      D.host.E (VS D) Λ F0.X D.sp.cm.cmUnram hlat hu hiso

  have hker : ∀ w ∈ perpS (VS D) F0.X, P' w = 0 := by
    intro w hw
    apply (VS D).nondeg.2
    intro x
    rw [← hadj x w]
    exact hw _ (hX x)
  refine ⟨fun b => P' (g0 b), ?_, ?_⟩
  · intro a b
    show (VS D).hT (F0.e a) (P' (g0 b)) = _
    rw [← hadj, hid _ (e_mem_X F0 a), hg0 a b]
  · intro v hv
    have hg0' : ∀ a b, (VS D).hT (F0.e a) (g0 b) = if a = b then 1 else 0 := hg0
    have hyc : ycL F0 (fun b => P' (g0 b)) v = P' (ycL F0 g0 v) := by

      rw [ycL_apply, ycL_apply, map_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])
    have hperp : v - ycL F0 g0 v ∈ perpS (VS D) F0.X := by
      apply mem_perp_of F0
      intro a

      rw [map_sub, ycL_apply, map_sum]
      simp [hg0']
    have h1 : P' (ycL F0 g0 v) = P' v := by
      have := hker _ hperp
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [hyc, h1]
    exact hint' v hv

theorem rowClass_of_zunit (h : RowZUnit) : RowClass :=
  rowClass_of_three row_dual_frame h trace_one_unramified

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassHolds

section

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_class_holds : RowClass := rowClass_of_zunit row_unit_condition

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
