module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLogStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCongruenceCombinationOverIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmallStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSecondBlockTangentBasisDualLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoordsNonunit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryOneCongrFrobenius

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondRoot

theorem charP_mvPowerSeries (σ k : Type) [Field k] (p : ℕ) [CharP k p] :
    CharP (MvPowerSeries σ k) p :=
  charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p

theorem coeff_pow_char_sum {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    coeff α (f ^ p) = ∑ m ∈ Finset.Iic α, if α = p • m then coeff m f ^ p else 0 := by
  classical
  haveI := charP_mvPowerSeries σ k p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set P : MvPowerSeries σ k := ∑ m ∈ Finset.Iic α, monomial m (coeff m f)
  set g := f - P
  have hg : ∀ m ≤ α, coeff m g = 0 := by
    intro m hm

    simp only [g, P, map_sub, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_Iic.2 hm) h
  have hmul : ∀ h : MvPowerSeries σ k, coeff α (h * g) = 0 := by
    intro h
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
    rw [hg q.2 (hq' ▸ le_add_self), mul_zero]
  have hf : f = P + g := by simp [g]
  have hgp : coeff α (g ^ p) = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    rw [hn, pow_succ]; exact hmul _
  rw [show f ^ p = (P + g) ^ p from congrArg (· ^ p) hf, add_pow_char, map_add (f := _), hgp, add_zero]
  simp only [P]

  rw [sum_pow_char, map_sum]
  simp only [monomial_pow, coeff_monomial]

theorem coeff_smul_pow_char {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (β : σ →₀ ℕ) : coeff (p • β) (f ^ p) = coeff β f ^ p := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [coeff_pow_char_sum, Finset.sum_eq_single β]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro hα
    exact hb (smul_right_injective _ hp0 hα).symm
  · intro hn
    exact absurd (Finset.mem_Iic.2 (le_smul_of_one_le_left zero_le (Nat.one_le_iff_ne_zero.2 hp0))) hn

theorem coeff_pow_char_of_not {σ k : Type} [DecidableEq σ] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : MvPowerSeries σ k) (α : σ →₀ ℕ) (h : ¬∃ β, p • β = α) : coeff α (f ^ p) = 0 := by
  classical
  rw [coeff_pow_char_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro hα; exact h ⟨b, hα.symm⟩

end GlobalTheory.SmallSecondRoot

namespace GlobalTheory.SmallSecondRoot

theorem exists_integral_cob1_congr_of_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv d μ hμ c t ht hct
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hroot : ∀ a : O, ∃ r : O, r ^ p = a := by
    intro a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Nat.pos_of_ne_zero hp0)
    have h1 : v z ≤ 1 := by
      have : v z ^ p ≤ 1 := by rw [← map_pow, hz]; exact hv.map_le_one a
      exact (pow_le_one_iff_of_nonneg zero_le hp0).1 this
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩
  choose rt hrt using hroot
  let u : MvPowerSeries (Fin d) O := fun β => rt (coeff (p • β) t)
  have hu : ∀ β, coeff β u = rt (coeff (p • β) t) := fun β => rfl
  refine ⟨u, fun α => ?_⟩
  let res := IsLocalRing.residue O
  have hres : ∀ x : O, ¬ IsUnit x ↔ res x = 0 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast res, ← hres]; exact Fact.out)
  have hμb : ∀ i, constantCoeff (map res (μ i)) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const i, map_zero]
  have ht' : map res t = (map res u) ^ p := by
    ext γ
    rw [coeff_map]
    by_cases h : ∃ β, p • β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [coeff_smul_pow_char, coeff_map, hu, ← map_pow, hrt]
    · rw [coeff_pow_char_of_not _ _ _ h, ← hres]
      apply ht
      by_contra hall
      push_neg at hall
      refine h ⟨Finsupp.mapRange (· / p) (Nat.zero_div p) γ, ?_⟩
      ext i
      simp [Nat.mul_div_cancel' (hall i)]
  have hcob : map res (cob1 μ t) = (cob1 (fun i => map res (μ i)) (map res u)) ^ p := by
    haveI := charP_mvPowerSeries (Fin d ⊕ Fin d) (IsLocalRing.ResidueField O) p
    rw [SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, ht']
    unfold cob1 inL inR
    rw [subst_pow (hasSubst_of_constantCoeff_zero hμb),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
      subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), sub_pow_char,
      sub_pow_char]
  have h1 := (hres _).1 (hct α)
  rw [map_sub, sub_eq_zero, ← coeff_map, hcob, coeff_smul_pow_char, map_pow] at h1
  have h3 : coeff α (cob1 (fun i => map res (μ i)) (map res u)) = res (coeff α c) :=
    frobenius_inj _ p h1
  rw [hres, map_sub, sub_eq_zero, ← h3, ← SmallSecond.map_formalGroupLawCoboundaryOne_eq res μ hμ.const, coeff_map]

end GlobalTheory.SmallSecondRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryOneCongrFrobeniusStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  first | exact @GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | exact GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | (intros; apply GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrame

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobComb

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_sum {ι : Type} [Fintype ι] (c : ι → B) (g : ι → MvPowerSeries σ Q)
    (hg : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  choose t ht using fun i => In.top_iff.1 (hg i)
  refine In.top_iff.2 ⟨∑ i, c i • t i, ?_⟩

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ht i, smul_eq_C_mul]

theorem frob_sum (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {ι : Type} [Fintype ι] (c : ι → Q)
    (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i, c i • f i) = ∑ i, s (c i) • frob p s (f i) := by
  have hX : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) := HasSubst.X_pow hp

  simp only [frob, ← coe_substAlgHom hX, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, map_smul]

end GlobalTheory.FrobComb

open GlobalTheory.FrobComb

theorem GlobalTheory.frob_comb_zero_left : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  intro p _ O _ _ _ ε F d k e U he b
  set b' : Fin d ⊕ Fin k → F.B := Sum.elim (fun _ => 0) b with hb'
  set c : Fin d ⊕ Fin k → F.B := fun j => F.σ (b' j) with hc
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ l i, (U * blk d k (p : F.B) 1) l i * c i = U l i * c i := by
    intro l i
    rcases i with i | i
    · simp [hc, hb']
    · simp [blk, Matrix.mul_diagonal]
  have hf : frob p F.s (comb b' e) = ∑ i, algebraMap F.B F.Q (c i) • frob p F.s (e i) := by
    rw [comb, frob_sum p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.s_alg]
  have hsplit : frob p F.s (comb b' e) - comb (U.mulVec c) e =
      ∑ i, algebraMap F.B F.Q (c i) •
        (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
    rw [hf]
    simp only [smul_sub, Finset.sum_sub_distrib]
    congr 1

    simp only [comb, Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, ← map_mul,
    map_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c _), key]
  rw [hsplit]
  exact in_top_sum c _ he
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrameStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  first | exact @GlobalTheory.frob_comb_zero_left | exact GlobalTheory.frob_comb_zero_left | (intros; apply GlobalTheory.frob_comb_zero_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoordsNonunitStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.tangent_coords_nonunit_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  first | exact @GlobalTheory.TangentIndep.tangent_coords_nonunit | exact GlobalTheory.TangentIndep.tangent_coords_nonunit | (intros; apply GlobalTheory.TangentIndep.tangent_coords_nonunit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallModMaximalOfFrobeniusImageSmall

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem small_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hc k e he hA U hU b hW j
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hC
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hc
  have hconst : ∀ i, constantCoeff (μ' i) = 0 := hμ'.const

  have hQL : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => hcμ ▸ ql_map hΘ μ' hconst (he.1 i)
  have hlog : ∀ i, cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := fun i =>
    hcμ ▸ formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hconst (hA i).1
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie p C v O hv ε hε F G d c μ' hμ' hc k e he hA Θ hΘ

  have hT := GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame p O ε F d k e U (fun i => (hU i).1) b
  have hC1 := GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog p O ε F d μ' hμ' (Fin d ⊕ Fin k) e he.1 (Sum.elim (fun _ => 0) b)
  obtain ⟨F₁, t, hF₁, hlin, hpβ, hα⟩ := GlobalTheory.T.frobenius_congruence_combination_over_integers p C v O hv ε F d c.μ μ' hμ' hc k e he.1 _ b hW hT hC1
  have ht := GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' p C v O hv d c.μ c.isLaw t hlin hα
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius p C v O hv d c.μ c.isLaw (map F.θ F₁) t ht
    (fun β => by rw [coeff_map]; exact hpβ β)
  have key : cob1 (up C c.μ) (comb (Sum.elim 0 fun j => F.θ (b j)) fun i => map Θ (e i)) =
      map (algebraMap O C) (map F.θ F₁) := by
    have h1 : (Sum.elim 0 fun j => F.θ (b j) : Fin d ⊕ Fin k → O) =
        fun i => F.θ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) i) := by
      funext i; rcases i with i | i <;> simp
    rw [h1, ← map_comb hΘ, ← hcμ, ← map_formalGroupLawCoboundaryOne_square hΘ μ' hconst, ← hF₁]
    ext α; simp [coeff_map, hΘ]
  refine GlobalTheory.T.tangent_coords_nonunit_alt p C v O hv G d c C hC k (fun i => map Θ (e i)) lb hQL hlb hlog
    (fun j => F.θ (b j)) u (fun α => ⟨_, hu α, ?_⟩) j
  rw [key, ← map_sub, coeff_map, map_sub]

end GlobalTheory.SmallSecond
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallModMaximalOfFrobeniusImageSmallStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.small_mod_maximal_of_frobenius_image_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  first | exact @GlobalTheory.SmallSecond.small_second | exact GlobalTheory.SmallSecond.small_second | (intros; apply GlobalTheory.SmallSecond.small_second <;> assumption)
end
end
