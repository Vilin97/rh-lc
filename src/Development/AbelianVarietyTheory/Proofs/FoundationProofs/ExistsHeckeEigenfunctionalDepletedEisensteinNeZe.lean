module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankinStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeightStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrence
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdgeStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenformStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  first | exact @GlobalTheory.EisM.eigF_of_prim | exact GlobalTheory.EisM.eigF_of_prim | (intros; apply GlobalTheory.EisM.eigF_of_prim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootsNormLeOfBoundedTwoStepRecurrenceStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence : ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) → ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  first | exact @GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | exact GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | (intros; apply GlobalTheory.roots_norm_le_of_bounded_two_step_recursion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FactorsAtL

theorem norm_one_of_pow {R : Type*} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    ‖z‖ = 1 := by
  have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this

theorem char_inv_facts {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Coprime N) :
    (χ⁻¹ (l : ZMod N)) ^ N.totient = 1 ∧ χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 hl
  constructor
  · obtain ⟨v, hv⟩ := hu
    rw [← hv, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · rw [show χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = (χ⁻¹ * χ) (l : ZMod N) from rfl, MulChar.inv_mul, MulChar.one_apply hu]

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

end GlobalTheory.FactorsAtL

namespace GlobalTheory.FactorsAtL

theorem factors_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l →
    α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  intro l _ ι e N χ g α β ζ he hN hlN hP hs hp hα ⟨n, hn, hζ⟩
  have hlp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨hut, huc⟩ := char_inv_facts hN χ l hcop
  have htot : 0 < N.totient := Nat.totient_pos.2 hN
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hinv0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hnl : ‖ι.symm (l : ℂ)‖ = (l : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_self l
  have hnζ : ‖ι.symm ζ‖ = 1 := norm_one_of_pow hn (by rw [← map_pow, hζ, map_one])
  have hnu : ‖ι.symm (χ⁻¹ (l : ZMod N))‖ = 1 := norm_one_of_pow htot (by rw [← map_pow, hut, map_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hαζ
    have hcα : ‖α‖ = 1 := by rw [hαζ]; exact Complex.norm_eq_one_of_pow_eq_one hζ hn.ne'
    have hcu : ‖χ⁻¹ (l : ZMod N)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hut htot.ne'
    have hβn : ‖β‖ = (l : ℝ) ^ (2 * e) := by
      have h := congrArg norm hp
      rw [norm_mul, norm_mul, hcα, hcu, norm_pow, Complex.norm_natCast, one_mul, one_mul] at h
      exact h
    obtain ⟨_, hrec, _⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hP
    obtain ⟨_, ⟨C, hC⟩, _⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hP.cf
    set u := χ⁻¹ (l : ZMod N) with hu_def
    let c : ℕ → ℂ := fun r => u ^ r * g (l ^ r)
    have hc0 : c 0 = 1 := by simp [c, hP.one]
    have hc1 : c 1 = α + β := by simp [c, hs]
    have hcr : ∀ r, c (r + 2) = (α + β) * c (r + 1) - α * β * c r := by
      intro r
      simp only [c]
      rw [hrec l r hlp hlN, hs, hp, show 2 * e + 1 - 1 = 2 * e by omega]
      have key : u ^ (r + 2) * χ (l : ZMod N) = u ^ (r + 1) := by rw [pow_succ, mul_assoc, huc, mul_one]
      linear_combination (-(l : ℂ) ^ (2 * e) * g (l ^ r)) * key
    set s := Real.sqrt l with hs_def
    have hs2 : s ^ 2 = l := Real.sq_sqrt hl0.le
    have hs1 : 1 < s := by rw [hs_def]; exact Real.lt_sqrt (by norm_num) |>.2 (by simpa using hl1)
    set R := s ^ (2 * e + 1) with hR
    have hR0 : 0 ≤ R := by positivity
    have hbound : ∀ r, ‖c r‖ ≤ Real.sqrt (max C 0) * R ^ r := by
      intro r
      have h1 : ‖c r‖ = ‖g (l ^ r)‖ := by
        simp only [c]; rw [norm_mul, norm_pow, hcu, one_pow, one_mul]
      have hX : ((l ^ r : ℕ) : ℝ) ^ (2 * e + 1) = (R ^ r) ^ 2 := by
        push_cast; rw [hR, ← hs2]; ring
      have h2 : ‖g (l ^ r)‖ ^ 2 ≤ max C 0 * (R ^ r) ^ 2 := by
        rw [← hX]; exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [h1, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (pow_nonneg hR0 r), ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h2
    obtain ⟨_, hβR⟩ := GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence α β c (Real.sqrt (max C 0)) R hR0 hc0 hc1 hcr hbound
    rw [hβn, ← hs2, ← pow_mul, hR] at hβR
    have : s ^ (2 * e + 1) < s ^ (2 * (2 * e)) := pow_lt_pow_right₀ hs1 (by omega)
    linarith
  · intro hβζ
    have h := congrArg (fun z => ‖ι.symm z‖) hp
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h
    rw [hα, hnu, hnl, one_mul, one_mul, hβζ, map_mul, norm_mul, hnl, hnζ, mul_one] at h
    have : ((l : ℝ)⁻¹) ^ (2 * e) < ((l : ℝ)⁻¹) ^ 1 := pow_lt_pow_right_of_lt_one₀ hinv0 hinv1 (by omega)
    rw [pow_one] at this
    linarith
  · intro j hj hαj
    rw [hαj, map_mul, map_pow, norm_mul, norm_pow, hnl, hnζ, mul_one] at hα
    have : ((l : ℝ)⁻¹) ^ j < 1 := pow_lt_one₀ hinv0.le hinv1 (by omega)
    linarith

end GlobalTheory.FactorsAtL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnityStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  first | exact @GlobalTheory.FactorsAtL.factors_ne_zero | exact GlobalTheory.FactorsAtL.factors_ne_zero | (intros; apply GlobalTheory.FactorsAtL.factors_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zv_unit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩

theorem zv_apply_ne_zero {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h
  have h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem zv_inv_mul {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ⁻¹ x * χ x = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ (zv_apply_ne_zero χ hx)

theorem zv_ch_changeLevel_mul {N l : ℕ} (cop : N.Coprime l) (A : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (d : ℤ) : ch (A.changeLevel (dvd_mul_right N l) * ψ.changeLevel (dvd_mul_left l N)) d = ch A d * ch ψ d := by
  unfold ch
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit ((d : ZMod (N * l)))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l)) := by
      rintro ⟨h1, h2⟩
      apply hu
      have : IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l))) := by
        rw [map_intCast]
        exact Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
      exact (isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this
    rcases not_and_or.mp hn with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

theorem zv_root {N l : ℕ} (hN : 0 < N) (cop : l.Coprime N) (θ : DirichletCharacter ℂ N) :
    ∃ n : ℕ, 0 < n ∧ (θ (l : ZMod N)) ^ n = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem eigF_value_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g →
    α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) →
    θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧
      val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ
  have hp : l.Prime := Fact.out
  have hl0 : 0 < l := hp.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have cop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight (N * l) hNl
  have hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hprod
  obtain ⟨B, c, hEig, hlam⟩ := GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'
  refine ⟨B, c, hEig, ?_⟩
  have hχm : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1

  obtain ⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d :=
    ⟨_, zv_ch_changeLevel_mul cop _ _⟩
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hθχ
    ext a
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cop (a : ZMod N).val 1
    haveI : NeZero N := ⟨hN.ne'⟩
    have hkN : ((k : ℕ) : ZMod N) = a := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]
    have hkl : ((k : ℕ) : ZMod l) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]
    have hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a := by
      rw [hφ]; unfold ch; push_cast; rw [hkN, hkl, map_one, mul_one]
    rw [h1] at hk
    unfold ch at hk
    rw [MulChar.one_apply_coe]
    by_cases hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))
    · rw [MulChar.one_apply hu] at hk; exact hk.symm
    · rw [MulChar.map_nonunit _ hu] at hk; exact absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)

  have hψ2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1) := by
    rw [hφ]; unfold ch; push_cast; rw [MulChar.mul_apply, hpar, hχm]

  obtain ⟨c₀, hFF⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (by unfold ch; push_cast; exact MulChar.map_zero ψ)
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun d _ => ⟨fun x => by unfold ch; push_cast; rw [map_mul, mul_comm],
      fun x => by unfold ch; push_cast; rw [map_mul, mul_comm]⟩)
    (by unfold ch; push_cast; rw [hpar]; linear_combination (-1 : ℂ) ^ e * hψ2)
  rw [mul_comm l N] at hFF

  have hat0 : hat φ 0 = 0 := ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 (N * l) φ hNl).2.2 hφ1
  obtain ⟨c₁, hE, hlat⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos
    hat0 (fun _ => rfl)
    (fun d hd => by
      have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime (by simpa using hd)
      refine ⟨fun y => ?_, fun x => by ring⟩
      unfold ch
      rw [map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])
    (by
      rw [mul_one]
      unfold ch
      rw [MulChar.inv_apply_eq_inv']
      have := hφm; unfold ch at this; rw [this]
      apply inv_eq_of_mul_eq_one_left
      have hm : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)
  rw [mul_one] at hE
  have hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1) := by
    simpa only [mul_one] using hE

  set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef
  set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef
  have hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E) := by
    have h1 := (GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).2 e (e + 1) (N * l) _ _ FF E hFF hE'
    rw [show e + (e + 1) = 2 * e + 1 by ring] at h1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime hd
    have hd' : IsCoprime d (N : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_left
    have hd'' : IsCoprime d (l : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_right
    have uN := zv_unit_of_isCoprime hd'
    have ul := zv_unit_of_isCoprime hd''
    have e1 := hφ d
    unfold ch at e1 ⊢
    rw [MulChar.mul_apply] at e1
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]
    have := zv_apply_ne_zero θ uN
    have := zv_apply_ne_zero χ uN
    have := zv_apply_ne_zero ψ ul
    field_simp
  have hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ := ((GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).1 FF E hFF.1 hE'.1).2
  obtain ⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ,
      lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ :=
    ⟨_, by
      have : ((N * l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNl.ne'
      have h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩
  have hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) =
      κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) := by
    intro h
    unfold pet
    rw [← integral_const_mul]
    congr 1
    funext τ
    rw [hqs]
    beta_reduce
    rw [hlat' τ]
    field_simp
  obtain ⟨P, hP0, hP1, hP2⟩ := GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF

  have copl : l.Coprime N := cop.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have fθ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)
  have fχ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)
  have hlamX : lam B c (mul FF E) ≠ 0 := by
    rw [hlam _ hX, hpet, hpet, hP1, hP2]
    intro h0
    have hl : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    have hκi : κ⁻¹ ≠ 0 := inv_ne_zero hκ
    have h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0 := by
      rw [← h0]; field_simp; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4
    · exact fθ.2.1 (by linear_combination -h4)
  exact GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE'
    hlamX fθ.1 (fχ.2.2 e he)

end GlobalTheory.EisM
end
end
end
