module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInductionStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInduction
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.TopIntersectionGrowthBoundStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPos

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.AmplePos

theorem pos_of_bound {h : ℕ → ℕ} {d C m₀ : ℕ} {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hf : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ h m)
    (hb : ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d| ≤
      C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) : 0 < a := by
  by_contra ha
  rw [not_lt] at ha
  obtain ⟨m, hm1, hm2⟩ := (hf.and_eventually (eventually_ge_atTop
    (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm2
  have hm1' : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  have hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m := by
    have h1 := Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))
    have h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hmK'
    push_cast at h2
    linarith
  have hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
    have h3 := (abs_le.mp (hb m hmm₀)).2
    have h4 : a * (m : ℤ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (by positivity)
    linarith
  have hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1)) := by
    have h5 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h5
    exact h5
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one] at hreal hm1
    linarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hreal hmK
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
    have h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) e
    have hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c := mul_pos hF hc
    rw [div_lt_iff₀ hFc] at hmK
    have h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤
        (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hF.le
    have hCpos : (0 : ℝ) ≤ C := by positivity
    have h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤
        (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hme : (0 : ℝ) < (m : ℝ) ^ e := by positivity
    have h8 := mul_lt_mul_of_pos_right hmK hme
    have h9 : (m : ℝ) ^ (e + 1) = m * m ^ e := by ring
    rw [h9] at h6
    nlinarith [h6, hreal, h7, h8]

theorem topSelf_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) →
    ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  intro k _ _ X _ _ hp d hd A hA
  obtain ⟨D, hD, c, hc, hf⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDd : D = d := by
    rw [hD] at hd
    exact_mod_cast hd
  subst hDd
  have hsupp : suppDim (structureModule X) ≤ (D : ℕ) := by
    unfold GlobalTheory.QCoh.suppDim
    rw [← hD]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨C, m₀, hb⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA
  rw [topSelf_def]
  exact pos_of_bound hc hf hb

end GlobalTheory.AmplePos
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPosStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) → ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  first | exact @GlobalTheory.AmplePos.topSelf_pos | exact GlobalTheory.AmplePos.topSelf_pos | (intros; apply GlobalTheory.AmplePos.topSelf_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmpleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | exact GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | (intros; apply GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonneg

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_cons_ample_nef_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  intro k _ _ X _ hp d hd H A hA P hP
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  have hv := diffVanish_chiPic_of_isProjOver hf (GlobalTheory.structureModule X) hp hsd
  obtain ⟨a, ha, s, hs, -⟩ := hA.exists_mono_cutHom (GlobalTheory.structureModule X)
  have hLa := isLB_lbPow hA.isLB a
  have h0 := H _ (suppDim_cut_le _ hLa s hsd) P hP
  rw [← interNum_cons_eq_interNum_cut hLa s hPb hfin] at h0
  have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons hA.isLB hPb) (0 : Fin (d + 1))
    hLa hA.isLB (a : ℤ) (cls_lbZPow hA.isLB a _)
  simp only [Fin.update_cons_zero] at h
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonnegStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  first | exact @GlobalTheory.interNum_cons_ample_nef_nonneg | exact GlobalTheory.interNum_cons_ample_nef_nonneg | (intros; apply GlobalTheory.interNum_cons_ample_nef_nonneg <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInductionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.nef_intersection_nonneg_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  first | exact @GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef | exact GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef | (intros; apply GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefIntegralStep

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem isAmpleLB_tens_lbPow_descent_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ (A N M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hM : M.IsLB) (q c : ℕ), 1 ≤ q → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ∀ b : ℕ, q ≤ b → b + 1 ≤ c * q → IsAmpleLB (tens (lbPow N q) (lbPow A (b + 1))) → IsAmpleLB (tens (lbPow N q) (lbPow A b)) := by
  intro k _ _ d hlow X _ _ hproj hdim A N M hA hN hM q c hq hMcls hbound b hqb hbc hL
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hdim' : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := hdim.le
  have hKl := GlobalTheory.T.nef_intersection_nonneg_induction k d hlow X hproj
  have hmix := GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg k X hproj d hdim' hKl A hA
  have hpos := GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos k X hproj (d + 1) hdim A hA
  have hNl := isLB_lbPow hN.isLB q
  have hAl : ∀ n : ℕ, (lbPow A n).IsLB := fun n => isLB_lbPow hA.isLB n
  have hLcls : cls _ hL.isLB = q • cls N hN.isLB + (b' + 1 + 1) • cls A hA.isLB := by
    rw [cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have hnum := GlobalTheory.T.top_intersection_growth_bound k X hproj d hdim' A N _ M hA hN hL hM hmix hpos q (b' + 1 + 1) c hq
    (by omega) hbc hLcls hMcls hbound
  have hB : IsAmpleLB (lbPow A 2) := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
  have hM'nef : IsNef k (tens (lbPow N q) (lbPow A b')) :=
    (hN.pow hA q).tens ((hA.isNef (k := k)).pow hA b') hA
  have hsplit : cls _ hL.isLB = cls _ hM'nef.isLB + cls _ hB.isLB := by
    rw [hLcls, cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]
    simp only [add_smul, one_smul, two_smul]
    abel
  have hsec := GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' k X hproj d hdim' _ _ _ hL hB hM'nef.isLB hsplit hnum
  have hamp := GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction k d hlow X hproj hdim' A _ hA hM'nef hsec
  have hT : (tens (lbPow N q) (lbPow A (b' + 1))).IsLB := isLB_tens hNl (hAl _)
  refine hamp.of_lbIso hT ((cls_eq_iff hT hamp.isLB).1 ?_)
  rw [cls_tens hNl (hAl _), cls_tens hA.isLB hM'nef.isLB, cls_tens hNl (hAl _), cls_lbPow hN.isLB,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB]
  simp only [add_smul, one_smul]
  abel
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefDimensionStep

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_descent : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro k _ _ d ih X _ _ hproj hdim A N hA hN
  have ampOfCls : ∀ {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M), cls L hL = cls M hM.isLB → IsAmpleLB L :=
    fun hL hM h => IsAmpleLB.of_lbIso hM hL ((cls_eq_iff hL hM.isLB).1 h)
  obtain ⟨c, hc1, hcM⟩ := exists_isAmpleLB_tens_lbPow k X hproj A N hA hN.isLB
  have hMLB : (tens N (lbPow A c)).IsLB := isLB_tens hN.isLB (isLB_lbPow hA.isLB c)
  have hMcls : cls (tens N (lbPow A c)) hMLB = cls N hN.isLB + c • cls A hA.isLB := by
    rw [cls_tens hN.isLB (isLB_lbPow hA.isLB c), cls_lbPow hA.isLB]
  set I := interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => tens N (lbPow A c)) : Fin (d + 1) → LB X)
  set q : ℕ := (2 * ((d : ℤ) + 1) * I).toNat + 1 with hqdef
  have hq1 : 1 ≤ q := by omega
  have hqlt : 2 * ((d : ℤ) + 1) * I < (q : ℤ) := by
    have := Int.self_le_toNat (2 * ((d : ℤ) + 1) * I)
    rw [hqdef]; push_cast; linarith
  have hP : ∀ b : ℕ, (tens (lbPow N q) (lbPow A b)).IsLB :=
    fun b => isLB_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b)
  have clsP : ∀ b : ℕ, cls _ (hP b) = q • cls N hN.isLB + b • cls A hA.isLB := by
    intro b
    rw [cls_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have base : IsAmpleLB (tens (lbPow N q) (lbPow A (c * q))) := by
    have hpow : IsAmpleLB (lbPow (tens N (lbPow A c)) q) := (isAmpleLB_pow_iff hMLB hq1).2 hcM
    refine ampOfCls (hP _) hpow ?_
    rw [clsP, cls_lbPow hMLB, hMcls, smul_add, smul_smul, mul_comm q c]
  have hcq : q ≤ c * q := by nlinarith
  have down : ∀ j : ℕ, j ≤ c * q - q → IsAmpleLB (tens (lbPow N q) (lbPow A (c * q - j))) := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j hj =>
      intro hj1
      have hprev := hj (by omega)
      have e : c * q - j = (c * q - (j + 1)) + 1 := by omega
      rw [e] at hprev
      exact isAmpleLB_tens_lbPow_descent_step k d ih X hproj hdim A N (tens N (lbPow A c)) hA hN hMLB q c hq1
        hMcls hqlt (c * q - (j + 1)) (by omega) (by omega) hprev
  have hqq := down (c * q - q) le_rfl
  have e2 : c * q - (c * q - q) = q := by omega
  rw [e2] at hqq
  have hTLB : (tens A N).IsLB := isLB_tens hA.isLB hN.isLB
  have hpow : IsAmpleLB (lbPow (tens A N) q) := by
    refine ampOfCls (isLB_lbPow hTLB q) hqq ?_
    rw [cls_lbPow hTLB, cls_tens hA.isLB hN.isLB, clsP, smul_add, add_comm]
  exact (isAmpleLB_pow_iff hTLB hq1).1 hpow

end GlobalTheory
end
end
