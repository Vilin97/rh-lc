module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ChrBij
public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
public import Formalism.StatementOC
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
import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.GzEq

section

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.Gz_eq :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by
  intro y
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hy : (n : ℝ) ≤ y := by
      have hk : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
      have hy0 : 0 ≤ y := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)] at hk
        exact lt_irrefl 0 hk
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)
    have hpos : (0 : ℝ) < n := by linarith
    have : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hpos, one_mul]
      exact hy
    rw [max_eq_left this]
  have hre : (Deduction.ramp (fun _ => 1) y).re
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_subset hsub]
    · simp [Deduction.ramp, Complex.re_sum]
    · intro n hn hn'
      have h0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hn'
        omega
      subst h0
      simp
  refine ⟨?_, ?_⟩
  · simp only [Formalism.Gz, Formalism.Sz, An.G]
    rw [hsum]
    ring
  · simp only [An.G, Deduction.G]
    rw [hre]
    ring
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.PrimInj

section

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.prim_inj :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by
  intro φ H
  constructor
  · intro θ θ' h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
    have h1 := (H.toHostRaw.isPrimOf_prim θ).2
    have h2 := (H.toHostRaw.isPrimOf_prim θ').2
    rw [← h] at h2
    have hc := ZMod.val_coe_unit_coprime u
    have e := (h1 _ hc).symm.trans (h2 _ hc)
    apply Units.ext
    rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
    simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
  · have hd : H.toHostRaw.dir 1 = 1 := by
      apply MulChar.ext
      intro u
      rw [HostRaw.dir_unit]
      simp
    rw [HostRaw.prim, hd, PChar.of_one]
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq

section

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.character_trivial_on_generator_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (s : φ.A) :
    chr φ ψ (φ.tau1 s) = 1 ↔ ψ (0, s) = 1 := by
  rw [← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]
  simp [toE, Frame.tau1, Frame.iotaInv, Frame.iota]
  exact Iff.rfl

private theorem UpperTheory.Comparison₂.gmA_eq_triv (φ : Frame) (θ : φ.Char) (hi : θ φ.iod = 1) :
    (∀ h : φ.A, θ (φ.tau1 h) = 1) ↔ θ = 1 ∨ θ = φ.psC := by
  constructor
  · intro h
    have hM : ∀ m : φ.MA, θ ((1, 1), m) = 1 := fun m => h (Multiplicative.toAdd m)
    have hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1 := by
      intro b
      rcases Int.units_eq_one_or b with rfl | rfl
      · exact θ.map_one
      · exact hi
    have hred : ∀ (a b : ℤˣ) (m : φ.MA), θ ((a, b), m) = θ ((a, 1), 1) := by
      intro a b m
      have e : (((a, b), m) : φ.GG) = ((a, 1), 1) * ((1, b), 1) * ((1, 1), m) := by
        ext <;> simp
      rw [e, map_mul, map_mul, hM, hB, mul_one, mul_one]
    have hsq : (θ φ.sg : ℂ) * (θ φ.sg : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have e : φ.sg * φ.sg = 1 := by
        simp only [Frame.sg]
        ext <;> simp
      rw [e, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp
      · simpa [Frame.sg] using h1
    · right
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp [Frame.psC, Frame.chQ]
      · simpa [Frame.psC, Frame.chQ, Frame.sg] using h1
  · rintro (rfl | rfl) h
    · simp
    · apply Units.ext
      simp [Frame.psC, Frame.chQ, Frame.tau1]

theorem UpperTheory.Comparison₂.gmA_eq :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by
  intro Λ φ H TT x eps C ell hE hell y
  classical
  obtain ⟨hbij, -, -, -, -⟩ := chr_bij φ
  obtain ⟨hpinj, hp1⟩ := prim_inj φ H
  have hmem : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw ↔ H.prim (chr φ ψ) ∈ Λ.KEPT := by
    intro ψ
    simp [keptA, HostRaw.kept_iff]
  have hXp : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw → chr φ ψ ∈ φ.Xp := by
    intro ψ hψ
    obtain ⟨θ, hθ, hpr⟩ := hE.kept _ ((hmem ψ).1 hψ)
    rw [HostRaw.isPrimOf_iff] at hpr
    have e := hpinj hpr
    rw [e]
    exact hθ
  have hKimg : Λ.KEPT = (keptA Λ H.toHostRaw).image (fun ψ => H.prim (chr φ ψ)) := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨θ, -, hpr⟩ := hE.kept p hp
      rw [HostRaw.isPrimOf_iff] at hpr
      obtain ⟨ψ, rfl⟩ := hbij.2 θ
      refine ⟨ψ, (hmem ψ).2 ?_, hpr.symm⟩
      rw [← hpr]
      exact hp
    · rintro ⟨ψ, hψ, rfl⟩
      exact (hmem ψ).1 hψ
  have hinj : Set.InjOn (fun ψ => H.prim (chr φ ψ)) (keptA Λ H.toHostRaw) :=
    fun a _ b _ h => hbij.1 (hpinj h)
  have hw : ∀ ψ ∈ keptA Λ H.toHostRaw, wtA (3 * (Λ.o : ℝ) + 1)⁻¹ ψ =
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) := by
    intro ψ hψ
    have hiod : chr φ ψ φ.iod = 1 := (hXp ψ hψ).2
    have htriv : (∀ h : φ.A, ψ (0, h) = 1) ↔ chr φ ψ = 1 ∨ chr φ ψ = φ.psC := by
      rw [← gmA_eq_triv φ (chr φ ψ) hiod]
      exact forall_congr' fun h => (character_trivial_on_generator_iff φ ψ h).symm
    obtain ⟨hps1, hps2⟩ := hE.ps
    unfold wtA
    by_cases hA : ∀ h : φ.A, ψ (0, h) = 1
    · rw [if_pos hA]
      rcases htriv.1 hA with h1 | h1
      · rw [h1, hp1, if_pos rfl]
      · have hK : H.toHostRaw.Kept Λ.KEPT φ.psC := by
          rw [HostRaw.kept_iff, ← h1]
          exact (hmem ψ).1 hψ
        rw [h1]
        split_ifs with hone
        · rfl
        · cases hk : Λ.psK with
          | none => exact absurd hK (hps2 hk)
          | some p =>
            have e := hps1 p hk
            rw [HostRaw.isPrimOf_iff] at e
            simp [Level.wt, hk, e]
    · rw [if_neg hA]
      have hn1 : chr φ ψ ≠ 1 := fun h => hA (htriv.2 (Or.inl h))
      have hnps : chr φ ψ ≠ φ.psC := fun h => hA (htriv.2 (Or.inr h))
      rw [if_neg (fun h => hn1 (hpinj (h.trans hp1.symm)))]
      unfold Level.wt
      rw [if_neg]
      intro hk
      have e := hps1 _ hk
      rw [HostRaw.isPrimOf_iff] at e
      exact hnps (hpinj e)
  have hG : ∀ ψ, (GPsi (arith H.toHostRaw) ell ψ y).re = (An.gChi (H.prim (chr φ ψ)).χ y).re := by
    intro ψ
    rw [(prim_read φ H ell hell ψ).2 y]
  have key : ∑ ψ ∈ keptA Λ H.toHostRaw,
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) *
        (An.gChi (H.prim (chr φ ψ)).χ y).re =
      ∑ p ∈ Λ.KEPT, (if p = PChar.one then 1 else Λ.wt p) * (An.gChi p.χ y).re := by
    rw [hKimg, Finset.sum_image hinj]
  have hone : (An.gChi PChar.one.χ y).re = An.G y := by
    have h1 : PChar.one.χ = 1 := rfl
    unfold An.gChi
    rw [if_pos h1]
    simp
  unfold GmA Level.Gm Level.Nt
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [hw ψ hψ, hG ψ]), key,
    ← Finset.add_sum_erase _ _ Λ.one_mem]
  congr 1
  · rw [if_pos rfl, one_mul, (Gz_eq y).1, hone]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_neg (Finset.ne_of_mem_erase hp)]
end
end
