module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeNoSecondWeightsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealKTypesInConeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExistsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracInequalityKTypes

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

section

@[expose] public section

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

theorem isLev_id (lam : Fin n → ℤ) : IsLev lam fun a => ((a : Fin n) : ℕ) := ⟨fun _ _ h => h, fun _ _ h => congrArg lam (Fin.ext h)⟩

theorem mem_harmSet {lam : Fin n → ℤ} {μ : Fin n → ℝ} (h : μ ∈ harmSet lam) :
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ μ = muQ lam fun a => (l a : ℕ) := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} (lev : Fin n → Fin n) (h : IsLev lam fun a => (lev a : ℕ)) :
    muQ lam (fun a => (lev a : ℕ)) ∈ harmSet lam := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lev, h, rfl⟩

def Compress : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ muQ lam (fun a => (l a : ℕ)) = muQ lam lev

theorem multG_of (hCp : Compress) (hM : MultFor) (hA : AdmLeast) (h1 : N1) (hC : ConeWeightsNotSecondType) (hE : ModelEx) (h7 : KTypeGenerationHighest) : MultG := by
  intro n lam hl V _ _ E1 E2 σ A hc
  classical
  have hne_h : (harmSet lam).Nonempty := ⟨_, muQ_mem_harmSet (fun a => a) (isLev_id lam)⟩
  by_cases hex : ∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥
  swap
  · push_neg at hex
    obtain ⟨μ₀, hμ₀⟩ := hne_h
    refine ⟨μ₀, hμ₀, fun μ hμ _ => hex μ hμ, ?_⟩
    intro v w hv _ hv0
    rw [hex μ₀ hμ₀, Submodule.mem_bot] at hv
    exact absurd hv hv0
  obtain ⟨μ₁, hμ₁, hne₁⟩ := hex
  let S := (harmSet lam).filter (fun μ => hwSp E1 E2 μ ≠ ⊥)
  have hSne : S.Nonempty := ⟨μ₁, Finset.mem_filter.mpr ⟨hμ₁, hne₁⟩⟩
  obtain ⟨μ₀, hμ₀S, hmin⟩ := S.exists_min_image (fun μ => nsq (μ + rhoV n)) hSne
  obtain ⟨hμ₀, hne₀⟩ := Finset.mem_filter.mp hμ₀S
  obtain ⟨l0, hl0, rfl⟩ := mem_harmSet hμ₀
  have hadm : AdmFor lam (fun a => (l0 a : ℕ)) E1 E2 := by
    refine hA n lam hl V E1 E2 σ A hc _ hl0 hne₀ ?_
    intro lev' hlev' hne'
    obtain ⟨l', hl', heq⟩ := hCp n lam lev' hlev'
    have hmem : muQ lam lev' ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hne'⟩
      rw [← heq]
      exact muQ_mem_harmSet l' hl'
    exact hmin _ hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₀
  refine ⟨_, hμ₀, ?_, ?_⟩
  · intro μ hμ hμne
    by_contra hb
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨M⟩ := hE n lam hl _ hl0
    have hMn2 : ∀ ν, IsSecondTypeWeight lam (fun a => (l0 a : ℕ)) ν → hwSp M.F1 M.F2 ν = ⊥ := by
      intro ν hν
      letI := M.nacg
      letI := M.ips
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact hC n lam hl _ hl0 ν (M.cone ν y hy hy0) hν
    obtain ⟨a, ha, hav⟩ := hc.irr v x hv0
    have hcone := h7 hM n lam hl _ hl0 V E1 E2 hc.pair hadm M hMn2 v hv hv0 μ x hx hx0 ⟨a, ha, hav⟩
    obtain ⟨l', hl', rfl⟩ := mem_harmSet hμ
    exact hμne (h1 n lam hl _ _ hl0 hl' hcone)
  · intro v' w hv' hw hv'0
    obtain ⟨a, ha, hav⟩ := hc.irr v' w hv'0
    exact hM n lam hl _ hl0 V E1 E2 hadm v' w hv' hw hv'0 ⟨a, ha, hav⟩

end PositivityTheory.RgBcC.RealD
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompressionStatement

section

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.real_compression : PositivityTheory.RgBcC.RealD.Compress := by
  first | exact @GlobalTheory.CompanionTheory.LevelCompress.exists_compress | exact GlobalTheory.CompanionTheory.LevelCompress.exists_compress | (intros; apply GlobalTheory.CompanionTheory.LevelCompress.exists_compress <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealFirstNilpotent

section

@[expose] public section

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.HarmCone

variable {n : ℕ}

def sg (lev : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (if lev a < lev b then 1 else 0) - (if lev b < lev a then 1 else 0)

theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) : 2 * rhoU lev a = ∑ b, sg lev a b := by
  simp only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]
  ring

theorem sg_anti (lev : Fin n → ℕ) (a b : Fin n) : sg lev a b = - sg lev b a := by
  unfold sg
  ring

theorem sg_cases (lev : Fin n → ℕ) (a b : Fin n) :
    sg lev a b = 1 ∨ sg lev a b = 0 ∨ sg lev a b = -1 := by
  unfold sg
  split_ifs <;> norm_num

theorem mul_sg_self (lev : Fin n → ℕ) (a b : Fin n) :
    ((lev a : ℝ) - lev b) * sg lev a b = -|(lev a : ℝ) - lev b| := by
  rcases lt_trichotomy (lev a) (lev b) with h | h | h
  · have h' : (lev a : ℝ) < lev b := by exact_mod_cast h
    have hs : sg lev a b = 1 := by
      unfold sg
      rw [if_pos h, if_neg (by omega)]
      norm_num
    rw [hs, abs_of_neg (by linarith)]
    ring
  · have hs : sg lev a b = 0 := by
      unfold sg
      rw [if_neg (by omega), if_neg (by omega)]
      norm_num
    rw [hs, h]
    simp
  · have h' : (lev b : ℝ) < lev a := by exact_mod_cast h
    have hs : sg lev a b = -1 := by
      unfold sg
      rw [if_neg (by omega), if_pos h]
      norm_num
    rw [hs, abs_of_pos (by linarith)]
    ring

theorem neg_abs_le_mul_sg (lev : Fin n → ℕ) (x : ℝ) (a b : Fin n) : -|x| ≤ x * sg lev a b := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith

theorem pair_root (f : Fin n → ℝ) (a b : Fin n) :
    ∑ x, f x * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) = f a - f b := by
  simp [mul_sub, Finset.sum_sub_distrib]

def dsg (lev lev' : Fin n → ℕ) (x b : Fin n) : ℝ := sg lev' x b - sg lev x b

theorem dsg_anti (lev lev' : Fin n → ℕ) (x b : Fin n) : dsg lev lev' x b = - dsg lev lev' b x := by
  unfold dsg
  rw [sg_anti lev' x b, sg_anti lev x b]
  ring

theorem dsg_nonneg (lev lev' : Fin n → ℕ) (x b : Fin n) :
    0 ≤ ((lev x : ℝ) - lev b) * dsg lev lev' x b := by
  unfold dsg
  rw [mul_sub, mul_sg_self]
  have := neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b
  linarith

theorem pairing_nonneg (lev lev' : Fin n → ℕ) :
    0 ≤ ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
  have e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [Finset.mul_sum]
  have e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    rw [Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dsg_anti lev lev' b x]
    ring
  have e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b
      = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b
  linarith

theorem harm_cone : N1 := by
  intro n lam _ lev lev' _ _ hc
  obtain ⟨c, hc0, hQ⟩ := hc
  have hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b := by
    intro x
    simp only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]
    ring
  have hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b
      = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) := by
    have e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) *
        ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) := by
      intro x
      rw [← hQx, hQ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]
  have hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
      have h2 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b)
      (hD ▸ pairing_nonneg lev lev')
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum
  have hz : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1
      (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
    have h3 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
    have h4 : (c a b : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h4 h
    · linarith
  funext x
  have h5 := hQ x
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5
  exact sub_eq_zero.1 h5

end GlobalTheory.CompanionTheory.HarmCone
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealFirstNilpotentStatement

section

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.real_first_nilpotent : PositivityTheory.RgBcC.RealD.N1 := by
  first | exact @GlobalTheory.CompanionTheory.HarmCone.harm_cone | exact GlobalTheory.CompanionTheory.HarmCone.harm_cone | (intros; apply GlobalTheory.CompanionTheory.HarmCone.harm_cone <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultGOfMultFor

section

@[expose] public section

namespace PositivityTheory.RgBcC.RealD

theorem multG_of_multFor (hM : MultFor) : MultG :=
  multG_of GlobalTheory.T.real_compression hM adm_least_holds GlobalTheory.T.real_first_nilpotent GlobalTheory.T.cone_no_second_weights GlobalTheory.T.real_model_exists GlobalTheory.T.real_k_types_in_cone

end PositivityTheory.RgBcC.RealD
end
end
