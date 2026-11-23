module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStableStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.Nat.Prime.Int
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonDoubleCosetAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChangeStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.heckeU_leftRepresentatives_level_change : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧ (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  first | exact @GlobalTheory.EisM.zrepU | exact GlobalTheory.EisM.zrepU | (intros; apply GlobalTheory.EisM.zrepU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeU

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RightRepU

lemma adj_repL (L l : ℕ) (j : Fin l) :
    (repL L l (some j)).adjugate = !![(1:ℤ), 0; -((L:ℤ) * ((j:ℕ):ℤ)), (l:ℤ)] := by
  simp [repL, Matrix.adjugate_fin_two_of]

lemma dvd_10 {L : ℕ} (γ : Gamma0 L) : (L:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

lemma not_dvd_00 {L l : ℕ} (hl : l.Prime) (hlL : l ∣ L) (γ : Gamma0 L) :
    ¬ (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 0 0 := by
  intro h
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)
  have h1 : (l:ℤ) ∣ 1 := by
    rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hl.one_lt.ne' (by exact_mod_cast this)

end GlobalTheory.EisM.RightRepU

namespace GlobalTheory.EisM.RightRepU

theorem rrep (L l : ℕ) (hl : l.Prime) (hlL : l ∣ L) (hL : 0 < L) :
    RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  haveI := Fact.mk hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hpr : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hlpos : (0:ℤ) < l := by exact_mod_cast hl.pos
  simp only [RRep, adj_repL]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, γ⟩ -
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul]
      rw [hdet, Matrix.det_fin_two_of]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using not_dvd_00 hl hlL γ
  · rintro ⟨j, γ⟩ - ⟨j', γ'⟩ - h
    simp only at h
    have e := fun r s => congrArg (fun M : M2 => M r s) h
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    obtain ⟨c1, hc1⟩ := dvd_10 γ
    obtain ⟨c1', hc1'⟩ := dvd_10 γ'
    have hLz : (0:ℤ) < L := by exact_mod_cast hL
    have hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1)) := by
      rw [hc1, hc1', ← h00] at h10
      linear_combination h10
    have hk2 := mul_left_cancel₀ hLz.ne' hk
    have hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0 := ⟨_, hk2⟩
    have hjj := (hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)
    have hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hjj
      have := j.isLt; have := j'.isLt
      rw [abs_lt]; constructor <;> omega
    have hjeq : j = j' := Fin.ext (by omega)
    subst hjeq
    have h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0 := by
      rw [← h00] at h10
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h10)
    have h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1 := by
      rw [← h01] at h11
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h11)
    refine Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))
    fin_cases r <;> fin_cases s
    · exact h00
    · exact h01
    · exact h10'
    · exact h11'
  · rintro δ ⟨hdet, hc, ha⟩
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c1, hc1⟩ := hc
    obtain ⟨L1, hL1⟩ := hlL
    have hLl : (L:ℤ) = l * L1 := by rw [hL1]; push_cast; ring
    have hd : (l:ℤ) ∣ δ 1 1 := by
      have : (l:ℤ) ∣ δ 0 0 * δ 1 1 :=
        ⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩
      exact (hpr.dvd_or_dvd this).resolve_left ha
    obtain ⟨d1, hd1⟩ := hd
    have ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ := ⟨_, rfl⟩
    let j : Fin l := ⟨x.val, ZMod.val_lt x⟩
    have hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, ZMod.natCast_val, ZMod.cast_id', id]
      rw [hx, mul_assoc, inv_mul_cancel₀ ha0]; ring
    obtain ⟨m, hm⟩ := hj
    let M : M2 := !![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]
    have hM : M.det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hlpos.ne'
      linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1
    let g : SL(2,ℤ) := ⟨M, hM⟩
    have hmem : g ∈ Gamma0 L := by
      rw [Gamma0_mem]; simp [g, M]
    refine ⟨(j, ⟨g, hmem⟩), trivial, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -(L:ℤ) * hm - hc1
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl

end GlobalTheory.EisM.RightRepU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeUStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU : ∀ L l : ℕ, 0 < L → l.Prime → l ∣ L → RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  first | exact @GlobalTheory.EisM.RightRepU.rrep | exact GlobalTheory.EisM.RightRepU.rrep | (intros; apply GlobalTheory.EisM.RightRepU.rrep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjoint

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem adjoint_U : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  intro k L N l ε ρ h a hk hL hNL hl hlL hlN hW hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hpos : 0 < l := hl.pos
  obtain ⟨-, hUa⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hpos ha.1
  have hcontH : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcontA : Continuous (qs a) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hModA : Mod (qs a) := GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1
  have hdet : ∀ j : Fin l, (repU l j).det = l := by
    intro j; simp [repU, Matrix.det_fin_two]
  have hint : ∀ i : Fin l, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repU l i) (qs a) τ * (τ.im : ℂ) ^ k)) := by
    intro i
    have hd : 0 < (repU l i).det := by rw [hdet]; exact_mod_cast hpos
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ _ hk hL hNL hW hh
      (((GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk).2.2.2.1 _ hd hcontA).aestronglyMeasurable)
      ((GlobalTheory.T.hasModerateGrowth_algebra_slash_stable).2.2 (qs a) k _ hd (by simp [repU]) hModA)
  have key := GlobalTheory.T.petersson_doubleCoset_adjoint k L N l ε ρ (DU L l) (Fin l) (Fin l) (repU l)
    (fun j => (repL L l (some j)).adjugate) (qs h) (qs a) hk hN hNL hpos hcop hW
    (by
      intro δ hδ
      obtain ⟨h1, h2, -⟩ := hδ
      exact ⟨h1, (Int.natCast_dvd_natCast.2 hNL).trans h2⟩)
    ((GlobalTheory.T.heckeU_leftRepresentatives_level_change L l hl).1 hlL) (GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU L l hL hl hlL) hh.1.2 ha.2 hcontH hcontA hint
  have e1 : qs (Uo l a) = hsum k (ch ε) (repU l) (qs a) := by
    funext τ
    rw [hUa τ]
    simp [hsum, repU, ch]
  have e2 : (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) =
      (fun τ => ∑ j, ch ε⁻¹ ((fun j => (repL L l (some j)).adjugate) j 0 0) *
        slz k ((fun j => (repL L l (some j)).adjugate) j).adjugate (qs h) τ) := by
    funext τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [repL, ch, Matrix.adjugate_fin_two_of]
  rw [e1, e2]
  exact key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeUAdjointStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  first | exact @GlobalTheory.adjoint_U | exact GlobalTheory.adjoint_U | (intros; apply GlobalTheory.adjoint_U <;> assumption)
end
end
