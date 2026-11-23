module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.DoubleCosetMeasures.Statement
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOneStatement

section

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → (∃ n, TypeDimAt P δ ν r t j n) ∧ ∃ z, StepAt P δ ν r t j z := by
  first | exact @GlobalTheory.TypeStep.exists_typeDim_step | exact GlobalTheory.TypeStep.exists_typeDim_step | (intros; apply GlobalTheory.TypeStep.exists_typeDim_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValueStatement

section

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.singleBlock_doublingIntegral_value : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t → StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  first | exact @GlobalTheory.Mem.SingleQ.stepAt_one | exact GlobalTheory.Mem.SingleQ.stepAt_one | (intros; apply GlobalTheory.Mem.SingleQ.stepAt_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace

section

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl


open Classical in
theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlaceStatement

section

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  first | exact @GlobalTheory.Mem.HD.RamBoth.ram_both | exact GlobalTheory.Mem.HD.RamBoth.ram_both | (intros; apply GlobalTheory.Mem.HD.RamBoth.ram_both <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty

section

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)


include hp hPv in
theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega


include hp hPv in
theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => GlobalTheory.T.singleBlock_doublingIntegral_value D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
end
end
end
