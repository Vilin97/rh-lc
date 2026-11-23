module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Data.ZMod.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEqStatement
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinked

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natCast_eq_le_prime {p n m : ℕ} (hp : 0 < p) (hn : n ≤ p) (hm : m ≤ p)
    (h : (n : ZMod p) = (m : ZMod p)) : n = m ∨ (n = 0 ∧ m = p) ∨ (n = p ∧ m = 0) := by
  have h' : n % p = m % p := (ZMod.natCast_eq_natCast_iff' n m p).1 h
  rcases hn.eq_or_lt with rfl | hn' <;> rcases hm.eq_or_lt with rfl | hm'
  · exact Or.inl rfl
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hm'] at h'
    exact Or.inr (Or.inr ⟨rfl, h'.symm⟩)
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hn'] at h'
    exact Or.inr (Or.inl ⟨h', rfl⟩)
  · rw [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hm'] at h'
    exact Or.inl h'

theorem eq_of_shifted_residues_eq :
    ∀ (p N : ℕ), p.Prime → ∀ (ν μ : Fin N → ℕ), Antitone ν → Antitone μ →
      (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) →
      (∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((ν i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card
        = (Finset.univ.filter fun i : Fin N => ((μ i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card) →
      μ = ν := by
  intro p N hp ν μ hν hμ h hc
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · funext i; exact i.elim0
  obtain ⟨h1, h2, h3⟩ := h hN
  have hp0 : 0 < p := hp.pos
  let a : Fin N → ℕ := fun i => ν i + (N - 1 - i.val)
  let b : Fin N → ℕ := fun i => μ i + (N - 1 - i.val)
  have hc' : ∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = x).card
      = (Finset.univ.filter fun i : Fin N => ((b i : ℕ) : ZMod p) = x).card := hc
  have ha : StrictAnti a := by
    intro i j hij
    have h4 := hν hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show ν j + (N - 1 - j.val) < ν i + (N - 1 - i.val)
    omega
  have hb : StrictAnti b := by
    intro i j hij
    have h4 := hμ hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show μ j + (N - 1 - j.val) < μ i + (N - 1 - i.val)
    omega
  let z : Fin N := ⟨0, hN⟩
  let l : Fin N := ⟨N - 1, by omega⟩
  have hal : a l = 0 := by
    show ν ⟨N - 1, _⟩ + (N - 1 - (N - 1)) = 0
    rw [h1]; omega
  have haz : a z ≤ p := by
    show ν ⟨0, hN⟩ + (N - 1 - 0) ≤ p
    omega
  have hbz : b z ≤ a z := by
    show μ ⟨0, hN⟩ + (N - 1 - 0) ≤ ν ⟨0, hN⟩ + (N - 1 - 0)
    omega
  have hzle : ∀ i : Fin N, z ≤ i := fun i => Nat.zero_le _
  have hap : ∀ i, a i ≤ p := fun i => (ha.antitone (hzle i)).trans haz
  have hbp : ∀ i, b i ≤ p := fun i => (hb.antitone (hzle i)).trans (hbz.trans haz)

  have two : ∀ i, a i = p → (∃ j, b j = 0) ∧ (∃ j, b j = p) := by
    intro i hi
    have hne : i ≠ l := by
      rintro rfl
      omega
    have h1lt : 1 < (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = 0).card := by
      refine Finset.one_lt_card.2 ⟨i, ?_, l, ?_, hne⟩
      · simp [hi]
      · simp [hal]
    rw [hc' 0] at h1lt
    obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.1 h1lt
    have e₁ : ((b j₁ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₁
    have e₂ : ((b j₂ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₂
    have r₁ := natCast_eq_le_prime hp0 (hbp j₁) hp0.le e₁
    have r₂ := natCast_eq_le_prime hp0 (hbp j₂) hp0.le e₂
    have hbne : b j₁ ≠ b j₂ := fun e => hj (hb.injective e)
    have s₁ : b j₁ = 0 ∨ b j₁ = p := by omega
    have s₂ : b j₂ = 0 ∨ b j₂ = p := by omega
    rcases s₁ with s₁ | s₁ <;> rcases s₂ with s₂ | s₂
    · exact absurd (s₁.trans s₂.symm) hbne
    · exact ⟨⟨j₁, s₁⟩, ⟨j₂, s₂⟩⟩
    · exact ⟨⟨j₂, s₂⟩, ⟨j₁, s₁⟩⟩
    · exact absurd (s₁.trans s₂.symm) hbne

  have sub : ∀ i, ∃ j, b j = a i := by
    intro i
    have hpos : 0 < (Finset.univ.filter fun k : Fin N => ((a k : ℕ) : ZMod p) = (a i : ZMod p)).card :=
      Finset.card_pos.2 ⟨i, by simp⟩
    rw [hc' (a i : ZMod p)] at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
    have ej : ((b j : ℕ) : ZMod p) = ((a i : ℕ) : ZMod p) := by simpa using hj
    rcases natCast_eq_le_prime hp0 (hbp j) (hap i) ej with e | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact ⟨j, e⟩
    · obtain ⟨k, hk⟩ := (two i e₂).2
      exact ⟨k, hk.trans e₂.symm⟩
    · have hbz' : b z = p := le_antisymm (hbp z) (e₁ ▸ hb.antitone (hzle j))
      have haz' : a z = p := le_antisymm haz (hbz' ▸ hbz)
      obtain ⟨k, hk⟩ := (two z haz').1
      exact ⟨k, hk.trans e₂.symm⟩
  have himg : Finset.univ.image a = Finset.univ.image b := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨j, hj⟩ := sub i
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    · rw [Finset.card_image_of_injective _ ha.injective,
        Finset.card_image_of_injective _ hb.injective]
  have hrange : Set.range b = Set.range a := by
    have := congrArg (fun s : Finset ℕ => (s : Set ℕ)) himg
    simpa using this.symm
  have hab : b = a := (StrictAnti.range_inj hb ha).1 hrange
  funext i
  have e : b i = a i := congrFun hab i
  have e' : μ i + (N - 1 - i.val) = ν i + (N - 1 - i.val) := e
  omega

end GlobalTheory.Alc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinkedStatement

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked : ∀ (p N : ℕ), p.Prime → ∀ (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((ν i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card = (Finset.univ.filter fun i : Fin N => ((μ i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card) → μ = ν := by
  first | exact @GlobalTheory.Alc.eq_of_shifted_residues_eq | exact GlobalTheory.Alc.eq_of_shifted_residues_eq | (intros; apply GlobalTheory.Alc.eq_of_shifted_residues_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcRow_succ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) (k : ℕ) :
    ∑ l, (hcMat R μ ^ (k+1)) i l =
      shift R μ i * ∑ l, (hcMat R μ ^ k) i l - ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ l, (hcMat R μ ^ k) j l := by
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpt : ∀ j : Fin N, hcMat R μ i j * ∑ l, (hcMat R μ ^ k) j l =
      (if j = i then shift R μ i * ∑ l, (hcMat R μ ^ k) j l else 0) +
      (if i < j then -∑ l, (hcMat R μ ^ k) j l else 0) := by
    intro j
    simp only [hcMat, Matrix.of_apply]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i < j
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq' , ← Finset.sum_filter,
    Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

def hcRowSeries (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : PowerSeries R :=
  PowerSeries.mk fun k => ∑ l, (hcMat R μ ^ k) i l

theorem hcRowSeries_eq (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) :
    (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) * hcRowSeries R μ i =
      1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j => i < j), hcRowSeries R μ j := by
  ext n
  cases n with
  | zero => simp [hcRowSeries, sub_mul, mul_assoc, Matrix.one_apply]
  | succ k =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hcRowSeries, sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, map_sum, hcRow_succ]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcTelescope (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    ∀ d, d ≤ N →
      (1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), hcRowSeries R μ j) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j + 1) * PowerSeries.X) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : Finset.univ.filter (fun j : Fin N => N - 0 ≤ j.val) = ∅ := by
      ext j; simp
    rw [this]; simp
  | succ d ih =>
    intro hd
    set i : Fin N := ⟨N - d - 1, by omega⟩ with hi
    have hS : Finset.univ.filter (fun j : Fin N => N - (d+1) ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin N => N - d ≤ j.val)) := by
      ext j; simp [hi, Fin.ext_iff]; omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      simp [hi]; omega
    have hgt : Finset.univ.filter (fun j : Fin N => i < j) = Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      ext j; simp [hi, Fin.lt_iff_val_lt_val]; omega
    have h := hcRowSeries_eq R N μ i
    rw [hgt] at h
    have IH := ih (by omega)
    rw [hS, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
    rw [map_add (f := _), map_one]
    linear_combination (1 - PowerSeries.C (shift R μ i) * PowerSeries.X - PowerSeries.X) * IH
      - PowerSeries.X * (∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X)) * h

theorem hcVal_generating (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) =
      ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  have h := hcTelescope R N μ N le_rfl
  have hU : Finset.univ.filter (fun j : Fin N => N - N ≤ j.val) = Finset.univ := by
    ext j; simp
  have hmk : PowerSeries.mk (hcVal R μ) = ∑ j, hcRowSeries R μ j := by
    ext n; simp [hcVal, hcRowSeries, map_sum]
  rw [hU] at h
  rw [hmk]
  exact h

end GlobalTheory.Alc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeriesStatement

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.traceEPowerHighestWeightValue_generating_series : ∀ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R), (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) = ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.Alc.hcVal_generating | exact GlobalTheory.Alc.hcVal_generating | (intros; apply GlobalTheory.Alc.hcVal_generating <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEq

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))
  have gν := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_
  refine GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
end
end
