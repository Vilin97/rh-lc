module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFactsStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesAcrZero

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.LSeq

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem lpow_nzd (n : ℕ) : (l : A.Acr0) ^ n ∈ nonZeroDivisors A.Acr0 :=
  pow_mem (A.acris_torsion_free l (Fact.out : l.Prime).ne_zero) n



def alphaL (n : ℕ) : A.Acr0 →ₗ[A.Acr0] (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ (n + 1)}) :=
  (Submodule.mkQ _).comp (LinearMap.mulLeft A.Acr0 ((l : A.Acr0) ^ n))


set_option synthInstance.maxHeartbeats 400000 in
def alpha (n : ℕ) : A.Acr 1 →+ A.Acr (n + 1) :=
  ((Ideal.span {(l : A.Acr0) ^ 1}).liftQ (alphaL A n) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker]
    simp only [alphaL, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)).toAddMonoidHom

theorem alpha_mk (n : ℕ) (y : A.Acr0) :
    alpha A n (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y) := rfl

theorem alpha_injective (n : ℕ) : Function.Injective (alpha A n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr 1 y = x := Ideal.Quotient.mk_surjective x
  rw [alpha_mk] at hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have h0 : (l : A.Acr0) ^ n * (y - c * (l : A.Acr0) ^ 1) = 0 := by
    rw [mul_sub, ← hc]; ring
  have h1 := mem_nonZeroDivisors_iff_left.1 (lpow_nzd A n) _ h0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, (sub_eq_zero.1 h1).symm⟩)

theorem alpha_exact (n : ℕ) : Function.Exact (alpha A n) (A.red n.le_succ) := by
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr (n + 1) y = x := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact ⟨A.mkAcr 1 c, by rw [alpha_mk, ← hc, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ : ∃ w, A.mkAcr 1 w = z := Ideal.Quotient.mk_surjective z
    rw [← red_mk A n.le_succ y, ← hz, alpha_mk, red_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨w, mul_comm _ _⟩)

theorem racrSeq (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcrSeq l :=
  fun n => ⟨fun A => alpha A n, fun A y => alpha_mk A n y, fun A => ⟨alpha_injective A n, alpha_exact A n⟩⟩

end GlobalTheory.CompanionTheory.LSeq
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFactsStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.acris_level_sequence_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := by
  first | exact @GlobalTheory.CompanionTheory.LSeq.racrSeq | exact GlobalTheory.CompanionTheory.LSeq.racrSeq | (intros; apply GlobalTheory.CompanionTheory.LSeq.racrSeq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltFacts

variable (l : ℕ) [Fact l.Prime]

theorem isDomain_ob : IsDomain (CrystallineSemistableComparison.Ob l) :=
  IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l

theorem norm_pFlat_eq : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ = ‖(l : ℂ_[l])‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]

theorem norm_pFlat_pos : 0 < ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ := by
  rw [norm_pFlat_eq]
  exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_pFlat_lt_one : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ < 1 := by
  rw [norm_pFlat_eq]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem rt_pow (k : ℕ) : CrystallineSemistableComparison.D.rt l k ^ l ^ k = pFlat l := by
  have h := (iterateFrobeniusEquiv (CrystallineSemistableComparison.Ob l) l k).apply_symm_apply (pFlat l)
  rwa [iterateFrobeniusEquiv_def] at h

theorem exists_dvd_pFlat_pow (a : CrystallineSemistableComparison.Ob l) (ha : a ≠ 0) : ∃ M : ℕ, a ∣ pFlat l ^ M := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 ha) (norm_pFlat_lt_one l)
  refine ⟨M, preTilt_dvd_iff_norm_le.2 ?_⟩
  rw [norm_pow]
  exact hM.le

theorem exists_rt_dvd (a : CrystallineSemistableComparison.Ob l) (ha : ¬ IsUnit a) : ∃ k : ℕ, CrystallineSemistableComparison.D.rt l k ∣ a := by
  have hlt : ‖a‖ < 1 := by
    refine lt_of_le_of_ne (preTilt_norm_le_one a) fun h => ha ?_
    exact (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rwa [preTilt_norm_def] at h)
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pFlat_pos l) hlt
  have hnl : n ≤ l ^ n := (Nat.lt_pow_self hl).le
  refine ⟨n, preTilt_dvd_iff_norm_le.2 ?_⟩
  have h1 : ‖a‖ ^ l ^ n ≤ ‖CrystallineSemistableComparison.D.rt l n‖ ^ l ^ n := by
    rw [← norm_pow (CrystallineSemistableComparison.D.rt l n), rt_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) hlt.le hnl).trans hn.le
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by omega)) (norm_nonneg _) h1

theorem obFacts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  intro l _
  haveI := isDomain_ob l
  refine ⟨inferInstance, ?_, exists_dvd_pFlat_pow l, exists_rt_dvd l⟩
  refine (ValuationRing.iff_dvd_total).2 ⟨fun a b => ?_⟩
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact Or.inr (preTilt_dvd_iff_norm_le.2 h)
  · exact Or.inl (preTilt_dvd_iff_norm_le.2 h)

end GlobalTheory.CompanionTheory.TiltFacts
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFactsStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.integral_ring_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  first | exact @GlobalTheory.CompanionTheory.TiltFacts.obFacts | exact GlobalTheory.CompanionTheory.TiltFacts.obFacts | (intros; apply GlobalTheory.CompanionTheory.TiltFacts.obFacts <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.AcrisModLBaseChange

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := GlobalTheory.T.integral_ring_facts

theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := GlobalTheory.T.acris_level_sequence_facts
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForD

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.R.forD (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RIn l :=
  ⟨RL.d_ob l, RL.acris_mod_l_base_change l, RL.d_seq l, fun A => ⟨(RL.u_tf A).1, fun x => by
    rw [← (RL.u_mod A).2, RingHom.mem_ker, sharpMap_coeff, Ideal.Quotient.eq_zero_iff_mem, pow_one]⟩, fun A n r => RL.gr A n r⟩
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem out : Out l := out_of_rin l (CrystallineSemistableComparison.R.forD l)

end CrystallineSemistableComparison.D
end
end
