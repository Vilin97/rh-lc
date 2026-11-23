module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
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
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData
public import Development.AutomorphicArithmetic.PrimitiveCosets.GChiEq
import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain
public import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypOfRpow

section

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHyp_of_rpow_eventually (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have h2 : 0 < η / 2 := by positivity
  have h1 := (tendsto_rpow_atTop h2).eventually_ge_atTop (K / (η / 2))
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (h1.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₁, fun Y hY => ?_⟩
  obtain ⟨ha, hb⟩ := hY₁ Y hY
  refine ⟨hb, ?_⟩
  have hY0 : 0 < Y := by linarith
  have hl := Real.log_le_rpow_div hY0.le h2
  have hp : 0 ≤ Y ^ (η / 2) := by positivity
  have he : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc K * Real.log Y ≤ K * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hl hK
    _ = K / (η / 2) * Y ^ (η / 2) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha hp
    _ = Y ^ η := he.symm

theorem windowHyp_of_rpow (F : CharFamily) {θ δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    WindowHyp F θ δ := by
  intro η hη Y₀
  obtain ⟨Y₁, hY₁⟩ := windowHyp_of_rpow_eventually (|C| * δ) η (by positivity) hη
  obtain ⟨Y, hY, hb⟩ := h (max Y₀ Y₁)
  obtain ⟨h1, hK⟩ := hY₁ Y (le_trans (le_max_right _ _) hY)
  have hY0 : 0 < Y := by linarith
  have hle : Y ≤ Y ^ (1 + δ) := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have heq : Set.EqOn (fun y : ℝ => |C| * y ^ θ * y ^ (-θ - 1)) (fun y : ℝ => |C| * y⁻¹)
      (Set.Icc Y (Y ^ (1 + δ))) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    simp only
    rw [mul_assoc, ← Real.rpow_add hy0, show θ + (-θ - 1) = -1 by ring, Real.rpow_neg_one]
  refine ⟨Y, le_trans (le_max_left _ _) hY, fun y => |C| * y ^ θ, ?_, ?_, ?_⟩
  · refine (integrableOn_congr_fun heq measurableSet_Icc).2 ?_
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (lt_of_lt_of_le hY0 hy.1).ne')
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    have hp : 0 ≤ y ^ θ := by positivity
    exact ⟨by positivity, (hb y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)⟩
  · rw [setIntegral_congr_fun measurableSet_Icc heq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hY0 (lt_of_lt_of_le hY0 hle),
      Real.log_div (lt_of_lt_of_le hY0 hle).ne' hY0.ne', Real.log_rpow hY0]
    calc |C| * ((1 + δ) * Real.log Y - Real.log Y) = |C| * δ * Real.log Y := by ring
      _ ≤ Y ^ η := hK

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp

section

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHypU_of_windowHyp_image (a b : ℝ) :
    Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h1
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h2

theorem windowHypU_of_windowHyp_fun (R : ℝ → ℝ) (θ : ℝ) :
    (fun u : ℝ => |Real.exp u| • (R (Real.exp u) * Real.exp u ^ (-θ - 1))) =
      fun u => R (Real.exp u) * Real.exp (-θ * u) := by
  funext u
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem windowHypU_of_windowHyp (F : CharFamily) {θ δ : ℝ} (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    WindowHypU (gm F) θ δ := by
  intro η hη U₀
  obtain ⟨Y, hY, R, hint, hR, hbound⟩ := h η hη (Real.exp U₀)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hS : Real.exp '' Icc (Real.log Y) ((1 + δ) * Real.log Y) = Icc Y (Y ^ (1 + δ)) := by
    rw [windowHypU_of_windowHyp_image, Real.exp_log hYpos, Real.rpow_def_of_pos hYpos, mul_comm]
  have hd : ∀ x ∈ Icc (Real.log Y) ((1 + δ) * Real.log Y),
      HasDerivWithinAt Real.exp (Real.exp x) (Icc (Real.log Y) ((1 + δ) * Real.log Y)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (Real.log Y) ((1 + δ) * Real.log Y)) :=
    Real.exp_injective.injOn
  refine ⟨Real.log Y, ?_, fun u => R (Real.exp u), ?_, ?_, ?_⟩
  · rw [← Real.exp_le_exp, Real.exp_log hYpos]; exact hY
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))).1 (by rw [hS]; exact hint)
    rw [windowHypU_of_windowHyp_fun] at this
    exact this
  · intro u hu
    have hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← hS]; exact ⟨u, hu, rfl⟩
    exact hR _ hmem
  · have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))
    rw [hS, windowHypU_of_windowHyp_fun] at e
    rw [← e]
    calc ∫ y in Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η := hbound
      _ = Real.exp (η * Real.log Y) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL

section

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

section

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.Imports

section

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  classical
  let weight (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else Λ.wt ψ
  have weight_pos (ψ : PChar) : 0 < weight ψ := by
    unfold weight Level.wt
    split_ifs
    · exact one_pos
    · exact one_pos
    · positivity
  have admissible (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
    by_cases h : ψ.χ = 1
    · left
      have hp := ψ.prim
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h
  let F : Deduction.CharFamily :=
    @Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne)
      (fun i => i.1.χ) (fun i => weight i.1) (fun i => weight_pos i.1)
      (fun i => admissible i.1)
  have hG (y : ℝ) : Deduction.Gm F y = Λ.Gm y := by
    change (∑ i : Λ.KEPT, weight i.1 * (Deduction.Gchi i.1.χ y).re) = Λ.Gm y
    rw [Finset.sum_coe_sort Λ.KEPT (fun ψ => weight ψ * (Deduction.Gchi ψ.χ y).re),
      ← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
    congr 1
    · have hGz : Formalism.Gz y = An.G y := by
        unfold Formalism.Gz Formalism.Sz An.G
        have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
            ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
          have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
          have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
          have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
            rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
            exact hny
          rw [max_eq_left hnonneg]
        rw [hsum]
        ring
      rw [show weight PChar.one = 1 by simp [weight], one_mul, ← gChi_eq, hGz]
      simp only [An.gChi, PChar.one]
      exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
      simp only [weight, ite_eq_right hne, gChi_eq]
  have hZ (h : Deduction.ZeroFree F θ) : Λ.ZeroFreeAbove θ := by
    intro ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  apply hZ
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

section

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key

end UpperTheory.Top

end
end
end
