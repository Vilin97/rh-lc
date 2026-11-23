module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EvaluationLiftDegreeZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FarRegOfLktUnitIneqFarNum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjROfVanKG
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjUOfInjR
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Polynomial.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SubChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TotalBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VNormSqRenum
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Tactic.Linter.HaveILetI
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasApplyOfScalChar

section

@[expose] public section

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest Cas etr epow)

namespace GlobalTheory.CompanionTheory.RgExhUnit

theorem etr_two_eq_cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : etr E 2 = Cas E := by
  simp [etr, Cas, epow]

theorem cas_apply_of_scalChar {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ)
    (hS : CompanionTheory.RgExh.ScalChar ⟨V, E, hE⟩ χ) (u : V) :
    Cas E u = (∑ a, χ a * χ a -
      ∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)) • u := by
  rcases n with _ | m
  · simp [Cas]
  · have h := GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V m E χ u hE
      (fun Y => by
        have := LinearMap.congr_fun (hS Y) u
        simpa using this) 2
    rw [etr_two_eq_cas, GlobalTheory.CasimirEigen.gelfVal_two_eq] at h
    exact h

theorem re_sum_mul_self {n : ℕ} (χ : Fin n → ℂ) :
    (∑ a, χ a * χ a).re = ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Complex.mul_re, sq]

theorem unitIneq : CompanionTheory.RgExh.U.UnitIneq := by
  intro n
  refine ⟨∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a, ?_⟩
  intro ε V _ _ E hE χ γ u hU hS hu hK
  have h1 := Formalism.REAL.wdCas V n ε E γ u hE hU hK
  have hin : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [cas_apply_of_scalChar V E hE χ hS u, inner_smul_right, hin] at h1
  have h2 := congrArg Complex.re h1
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hsum : 0 ≤ ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    split_ifs <;> positivity
  have hrho : (∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)).re =
      ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.mul_re]
  have hc : (∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a) * ‖u‖ ^ 2 =
      (Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε)) * ‖u‖ ^ 2 -
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    rw [Complex.re_mul_ofReal, Complex.ofReal_re, Complex.sub_re, re_sum_mul_self, hrho] at h2
    exact h2
  have hnn : 0 ≤ Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    show 0 ≤ ∑ a, Formalism.REAL.rhoC ε a * Formalism.REAL.rhoC ε a
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hle : ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a ≤
      Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    refine le_of_mul_le_mul_right ?_ hpos
    rw [hc]
    linarith
  show _ ≤ Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) + _
  linarith

end GlobalTheory.CompanionTheory.RgExhUnit
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantOfKHighest

section

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg

open Finset
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

lemma kRel_of_glRel {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) : CompanionTheory.D.DSIC.KRel ε E :=
  fun a b c d _ _ => hE a b c d

lemma kUnit_of_isUnitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) : CompanionTheory.D.DSIC.KUnit ε E := by
  intro a b he x y
  rw [hU a b x y]
  simp [Formalism.REAL.sgn, he]

lemma dominant_of_kHighest {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hF : CompanionTheory.D.DSIC.KRel ε E) (hU : CompanionTheory.D.DSIC.KUnit ε E)
    {μ : Fin n → ℝ} {u : V} (hu : u ≠ 0) (hh : KHighest ε E μ u) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    μ b ≤ μ a := by
  have h := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1
  rw [hh.2 a b hab he, norm_zero] at h
  have hp : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  by_contra hc
  push Not at hc
  have : 0 < (μ b - μ a) * ‖u‖ ^ 2 := mul_pos (by linarith) hp
  have := sq_nonneg ‖E b a u‖
  nlinarith

lemma two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, ((2 : ℝ) • rhoC ε) a = m := by
  refine ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  simp only [Pi.smul_apply, rhoC, smul_eq_mul]
  push_cast
  ring

lemma vNormSq_nat (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : ∀ a, ∃ m : ℤ, μ a = m) :
    ∃ k : ℕ, vNormSq ε μ = k := by
  choose m hm using hμ
  choose r hr using two_rhoC_int ε
  refine ⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩
  have h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2 := by
    intro a
    have h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    have h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1, hm a, hr a]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [h a, sq]

theorem lktExists : LKTExists := by
  classical
  intro n ε V _ _ E hE hV hU hfin hint
  have hF : CompanionTheory.D.DSIC.KRel ε E := kRel_of_glRel hE
  have hK : CompanionTheory.D.DSIC.KUnit ε E := kUnit_of_isUnitary hU
  have hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m :=
    fun μ x hx hh => hint μ x hx hh.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨S, hfd, hS, hxS⟩ := hfin x
  obtain ⟨y, -, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS
    (fun h => hx (by simpa [h] using hxS))
  have hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k := by
    obtain ⟨k, hk⟩ := vNormSq_nat ε (hintK ν y hy0 hy)
    exact ⟨k, ν, y, hy0, hy, hk⟩
  obtain ⟨γ, u, hu, hγ, hk⟩ := Nat.find_spec hex
  refine ⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩
  intro μ w hw hμ
  obtain ⟨k, hk'⟩ := vNormSq_nat ε (hintK μ w hw hμ)
  rw [hk, hk']
  exact_mod_cast Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩

end GlobalTheory.CompanionTheory.RgExhFarReg
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NumKG

section

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ClusterNum

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq abs_sig)
open PI.UpqRep

theorem numKG : NumKG := by
  intro n ε γ lev ν B C hG hB hBn hC _ hdom hn
  set X := xv ε γ with hX
  set κ := X - rhoC ε - wt B with hκ
  set μ := X - wt B - wt C with hμ
  obtain ⟨hXa, -, hgap⟩ := hG
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  have hκw := sorted_weight_eq_of_norm_eq ε κ μ ν C hC w hw hs (hdom w hw)
    (fun a => by simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring) hn
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => (hBn _ h2).1 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hcd' : c < d := hcd
  have hne : t c d = -1 := by
    have h1 : ¬ε c = ε d := (hBn _ hi).1
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have hgcd : Lc n ≤ X c - X d := hgap c d (hBn _ hi).2

  have p1 := pair_eq t ta X
  have p2 := pair_eq sig sig_anti X
  have hD : ∀ a b, 0 ≤ sig a b * (X a - X b) - t a b * (X a - X b) := fun a b => by
    rw [sig_mul hXa, sub_nonneg]
    exact (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (tb' a b))
  have hDcd : 2 * Lc n ≤ sig c d * (X c - X d) - t c d * (X c - X d) := by
    rw [hne, show sig c d = 1 by simp [sig, hcd']]
    linarith
  have hsum : ∑ a, ∑ b, t a b * (X a - X b) + 2 * Lc n ≤ ∑ a, ∑ b, sig a b * (X a - X b) := by
    have h1 : sig c d * (X c - X d) - t c d * (X c - X d) ≤
        ∑ a, ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)) :=
      (Finset.single_le_sum (f := fun b => sig c b * (X c - X b) - t c b * (X c - X b))
        (fun b _ => hD c b) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)))
        (fun a _ => Finset.sum_nonneg fun b _ => hD a b) (mem_univ c))
    simp only [Finset.sum_sub_distrib] at h1
    linarith
  have hy : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) := fun a => by
    have h1 := hκw (w.symm a)
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    have ts : ∑ b, t a b = ∑ b, sig a b - ∑ b, sc ε a b - 2 * ∑ b, (ind B a b - ind B b a) +
        ∑ b, sc ε (w.symm a) (w.symm b) := by
      simp only [t]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b),
        Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]
    simp only [hκ, Equiv.apply_symm_apply, Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ts]
    linarith
  have hY : ∀ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := fun a => by
    have e : (∑ b, t a b) / 2 - (∑ b, sig a b) / 2 = (∑ b, (t a b - sig a b)) / 2 := by
      rw [Finset.sum_sub_distrib]; ring
    have h2 : |∑ b, (t a b - sig a b)| ≤ 2 * (n : ℝ) := by
      calc _ ≤ ∑ b, |t a b - sig a b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin n, (2 : ℝ) := Finset.sum_le_sum fun b _ => by
            have := abs_sub (t a b) (sig a b)
            linarith [tb' a b, abs_sig a b]
        _ = 2 * (n : ℝ) := by simp [mul_comm]
    rw [e, div_pow]
    have h3 : (∑ b, (t a b - sig a b)) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  have g1 : vNormSq ε ν = ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 := by
    unfold vNormSq nsq dot
    rw [← Equiv.sum_comp w.symm]
    exact Finset.sum_congr rfl fun a _ => by rw [hy, sq]
  have g2 : vNormSq ε γ = ∑ a, X a ^ 2 := by
    unfold vNormSq nsq dot
    exact Finset.sum_congr rfl fun a _ => (sq _).symm
  have g3 : ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 = ∑ a, X a ^ 2 +
      (2 * ∑ a, X a * ((∑ b, t a b) / 2) - 2 * ∑ a, X a * ((∑ b, sig a b) / 2)) +
      ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have g4 : ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc _ ≤ ∑ _a : Fin n, (n : ℝ) ^ 2 := Finset.sum_le_sum fun a _ => hY a
      _ = (n : ℝ) ^ 3 := by simp; ring
  have g5 : (n : ℝ) ^ 3 < Lc n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Lc
    nlinarith [pow_le_pow_left₀ h0 (by linarith : (n : ℝ) ≤ n + 1) 3, pow_pos (by linarith : (0 : ℝ) < n + 1) 3]
  rw [g1, g2, g3]
  linarith

end GlobalTheory.CompanionTheory.ClusterNum
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VanKGOf

section

@[expose] public section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhVanKG

open CompanionTheory.D.LK
open CompanionTheory.D.LK.Car
open CompanionTheory.RgExh.U
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem vanKG_of (hN : NumKG) : VanKG := by
  have hC : COK := cok_of hGenCO
  have hP : WtProj := GlobalTheory.CompanionTheory.LKWtProj.wtProj
  have hM : WtMajor := GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of CompanionTheory.D.DSIC.hLowSpan
  intro n ε γ lev V _ _ E hg hE hU hF hmin B j z hB hBU hz hwt hb
  set τ := xv ε γ with hτ
  apply exists_boundary_of_weight_obstruction hC hP hM ε E hE hU hF B j τ z hz hwt hb
  intro A hA ν y hy0 hy hd hc hnorm
  have hA1 := (hz A hA).1
  refine absurd (hmin ν y hy0 hy) (not_le.2 (hN n ε γ lev ν B (A.filter (cpt ε)) hg hB
    (fun i hi => ⟨(mem_filter.1 (hA1.symm ▸ hi :)).2, hBU i hi⟩) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
  · convert hc w hw' using 2
    funext c
    simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
    ring
  · rw [← hnorm]
    congr 1
    abel

end GlobalTheory.CompanionTheory.RgExhVanKG
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.FarRegularExhaustion

section

@[expose] public section

namespace CompanionTheory.RgExh.U

theorem far_regular_exhaustion : CompanionTheory.RgExh.FarReg :=
  GlobalTheory.CompanionTheory.FarRegularityLevels.farReg_of_lkt_unitIneq_farNum GlobalTheory.CompanionTheory.RgExhFarReg.lktExists GlobalTheory.CompanionTheory.RgFarRen.renumber GlobalTheory.CompanionTheory.RgExhUnit.unitIneq
    (GlobalTheory.CompanionTheory.RgCOBlock.coBlock (GlobalTheory.CompanionTheory.RgExh.injU_of_injR (GlobalTheory.CompanionTheory.RgExhInjR.injR_of_vanKG
      (GlobalTheory.CompanionTheory.RgExhVanKG.vanKG_of GlobalTheory.CompanionTheory.ClusterNum.numKG))) GlobalTheory.CompanionTheory.GenCOUP.genCOU) GlobalTheory.CompanionTheory.RgExhFar.farNum

end CompanionTheory.RgExh.U
end
end
