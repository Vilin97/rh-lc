module

public import Formalism.PeriodIntegrals.FglPtW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm

section

@[expose] public section

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem addGen_thm : PI.FglPtW.AddGen := by
  intro K _ S l ex hex0 hinv hF σ a b ha hb
  have hcc : ∀ {τ : Type} (f : PowerSeries K) (c : MvPowerSeries τ K),
      MvPowerSeries.constantCoeff c = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst c f) = PowerSeries.constantCoeff f := by
    intro τ f c hc
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [map_pow, hc, zero_pow hd, smul_zero]
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := hcc l ex hex0
    rw [hinv] at h
    rw [← h]
    exact PowerSeries.constantCoeff_X
  have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ K) s) = 0 := by
    intro s
    fin_cases s <;> simp [ha.2, hb.2]
  have hP : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  have hmix : ∀ (c : MvPowerSeries (Fin 2) K), MvPowerSeries.constantCoeff c = 0 →
      ∀ f : PowerSeries K, MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst c f) =
        PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) c) f := by
    intro c hc f
    exact MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hc)) hP f
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hG0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add (f := _), hcc l _ hX0, hcc l _ hX1, hl0, add_zero]
  have hG : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) =
      PowerSeries.subst a l + PowerSeries.subst b l := by
    rw [MvPowerSeries.subst_add hP, hmix _ hX0, hmix _ hX1, MvPowerSeries.subst_X hP,
      MvPowerSeries.subst_X hP]
    rfl
  have heq : PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
      MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) := by
    rw [hmix _ hG0, hG]
  refine ⟨?_, ?_⟩
  · rw [heq, serOver_iff]
    refine mvsubst_mem_SerS S hP0 (fun i => ?_) ((serOver_iff S _).mp hF)
    fin_cases i <;> simp [(serOver_iff S a).mp ha.1, (serOver_iff S b).mp hb.1]
  · rw [hcc ex _ (by rw [map_add (f := _), hcc l a ha.2, hcc l b hb.2, hl0, add_zero])]
    exact hex0

end PI.FglPtW.Wk

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm

section

@[expose] public section

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem mulGen_thm : PI.FglPtW.MulGen := by
  intro K _ S l ex hex hl c hG σ a ha
  obtain ⟨haS, ha0⟩ := ha
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero hex'

  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h1 := congrArg MvPowerSeries.constantCoeff hl
    rw [PowerSeries.constantCoeff_subst hsub,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
    simpa using h1.trans (PowerSeries.constantCoeff_X (R := K))
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0 := by simp
  have hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX0
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  have hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]
  have hAs := PowerSeries.HasSubst.of_constantCoeff_zero hA0

  have hinner : PowerSeries.subst a (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) =
      MvPowerSeries.C c * PowerSeries.subst a l := by
    rw [← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hXs has]
    congr 1
    · have h2 := (PowerSeries.substAlgHom has).commutes c
      rw [PowerSeries.coe_substAlgHom] at h2
      first
        | exact h2
        | simp
        | (simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
           exact h2)
    · congr 1
      exact PowerSeries.subst_X has
  have key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex =
      PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c *
        PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) := by
    rw [PowerSeries.subst_comp_subst_apply hAs has, hinner]
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [serOver_iff]
    exact subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)
  · exact PowerSeries.constantCoeff_subst_eq_zero ha0 _
      (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)

end PI.FglPtW.Wk

end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW

section

@[expose] public section

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]
end
end
