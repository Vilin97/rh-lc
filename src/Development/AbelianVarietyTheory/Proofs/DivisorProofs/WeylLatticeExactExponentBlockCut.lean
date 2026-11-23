module

public import Formalism.PieriBlockIdeals.StatementE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionStStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperatorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvarianceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvarianceStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBound

section

@[expose] public section

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

theorem adj_sub_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) : adj (x - y) = adj x - adj y := by
  ext T
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  noncomm_ring

theorem adj_zero_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] : adj (0 : A) = 0 := by
  ext T
  simp [adj]

theorem adj_commutator_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) :
    adj x * adj y - adj y * adj x = adj (x * y - y * x) := by
  ext T
  simp only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    map_sub]
  noncomm_ring

theorem adjBdd_holds : AdjBdd := by
  intro V _ _ N K e hrel hbdd hspan
  constructor
  · intro a b c d ha hb hc hd
    rw [adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]
    split_ifs <;> simp [adj_zero_of_adjBdd]
  · intro a ha b hb n T hT hn
    have hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x := by
      rintro x ⟨μ, hμ⟩
      simp only [LinearMap.zero_apply]
      by_cases hx : x = 0
      · simp [hx]
      have h1 : μ b - μ a ≤ K := by
        by_contra hlt
        push_neg at hlt
        apply hx
        apply hbdd b hb a ha (μ b - μ a) x _ hlt
        rw [hμ b hb, hμ a ha]
        push_cast
        rw [sub_smul]
      apply hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)
      have eq := LinearMap.congr_fun hT x
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq
      push_cast
      rw [add_smul, sub_smul, ← eq]
      abel
    exact LinearMap.ext_on hspan hw

end GlobalTheory.LeviCut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBoundStatement

section

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  first | exact @GlobalTheory.LeviCut.adjBdd_holds | exact GlobalTheory.LeviCut.adjBdd_holds | (intros; apply GlobalTheory.LeviCut.adjBdd_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBound

section

@[expose] public section

open GlobalTheory.LeviCut

namespace GlobalTheory.BetaDenProof

theorem dvd_lam_of_le {l w t : ℕ} (hl : l.Prime) (ht : 1 ≤ t) (htw : t ≤ w) :
    t ∣ (∏ s ∈ Finset.Icc 1 w, ordCompl[l] s) * l ^ Nat.log l w := by
  have ht0 : t ≠ 0 := by omega
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self t l]
  rw [mul_comm (ordProj[l] t)]
  apply Nat.mul_dvd_mul
  · exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ht, htw⟩)
  · apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le hl.one_lt
    exact (Nat.ordProj_le l ht0).trans htw

theorem beta_dvd {Λ w : ℕ} (h : ∀ t, 1 ≤ t → t ≤ w → t ∣ Λ) :
    ∀ k j : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial) := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [Nat.add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]
    exact Nat.mul_dvd_mul (h (j + 1) (by omega) (by omega)) dvd_rfl
  | succ k ih =>
    intro j hj
    have h1 := ih j (by omega)
    have h2 := ih (j + 1) (by omega)
    have e : Λ * (j.factorial * (k + 1).factorial) + Λ * ((j + 1).factorial * k.factorial)
        = (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      rw [Nat.factorial_succ k, Nat.factorial_succ j]; ring
    have hA : (j + (k + 1) + 1).factorial ∣ (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      have : (j + (k + 1) + 1).factorial = (j + k + 2) * (j + k + 1).factorial := by
        rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, Nat.factorial_succ]
      rw [this]; exact Nat.mul_dvd_mul dvd_rfl h1
    have hB : (j + (k + 1) + 1).factorial ∣ Λ * ((j + 1).factorial * k.factorial) := by
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]; exact h2
    rw [← e] at hA
    exact (Nat.dvd_add_left hB).mp hA

end GlobalTheory.BetaDenProof

theorem GlobalTheory.LeviCut.betaDen : GlobalTheory.LeviCut.BetaDen := by
  intro l w hl
  refine ⟨∏ s ∈ Finset.Icc 1 w, ordCompl[l] s, ?_, ?_⟩
  · intro hd
    obtain ⟨s, hs, hds⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    have : s ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
    exact Nat.not_dvd_ordCompl hl this hds
  · intro j k hjk
    exact GlobalTheory.BetaDenProof.beta_dvd (fun t ht htw => GlobalTheory.BetaDenProof.dvd_lam_of_le hl ht htw) k j hjk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBoundStatement

section

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.beta_integral_denominator_bound : GlobalTheory.LeviCut.BetaDen := by
  first | exact @GlobalTheory.LeviCut.betaDen | exact GlobalTheory.LeviCut.betaDen | (intros; apply GlobalTheory.LeviCut.betaDen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe {N : ℕ} (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    (eV N ν a b x : MvPolynomial (Fin N × Fin N) ℚ) = LR.der N N a b x := by
  unfold eV
  rw [dite_eq_left ⟨a.2, b.2⟩]
  rfl

theorem cut_incl (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ K w Λ : ℕ)
    (h₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)),
      (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (h₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
      (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (hK : ∀ i j, ν i ≤ ν j + K) (hw' : K + (p + q) ≤ w + 1)
    (hΛ : ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) :
    ∀ x ∈ dualWeyl ℤ (p + q) (p + q) ν, ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x ∈ weyl ℤ (p + q) (p + q) le_rfl ν := by
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hL p q ν hν c₁ c₂ h₁ h₂
  obtain ⟨hrel, hspan, hdom, hst1, hst2⟩ := hN (p + q) ν hν
  obtain ⟨hrel', hbdd'⟩ := hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan
  set e := eV (p + q) ν with he
  set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀
  have hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0 :=
    hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hT1 c hc d hd hcd, sub_self])
  let v : dualWeyl ℚ (p + q) (p + q) ν := ⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩
  let φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ :=
    { toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
      map_add' := fun x y => LR.fock_add_right _ _ _
      map_smul' := fun c x => LR.fock_smul_right _ _ _ }
  have hwz : ∀ c : Fin (p + q), wtZ ν c = ν c := fun c => by simp [wtZ]
  have hv : IsWt (p + q) e (wtZ ν) v := by
    intro c hc
    apply Subtype.ext
    have h1 := eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v
    have h2 := (LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩
    have h3 := hwz ⟨c, hc⟩
    simp only at h1 h3
    rw [he, h1, h3]
    simpa using h2
  have hsc := hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by
    have hi : i < p + q := hij.trans hj
    have hr := LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij
    have h3 := hwz ⟨i, hi⟩
    have h4 := hwz ⟨j, hj⟩
    simp only at h3 h4
    refine ⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩
    · exact (eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr
    · have h1 := eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x
      change fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
      simp only at h1
      rw [h1, ← LR.fock_der, hr]
      simpa using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    · rw [h3, h4]; exact_mod_cast hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)
    · rw [h3, h4]; exact_mod_cast hK _ _) hT3
  set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz
  have hone : (z : ℚ) • S₀ = 1 := by
    refine hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_
    · have := hinv c hc d hd
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [mul_smul_comm, smul_mul_assoc, ← he, this]
    · change φ (((z : ℚ) • S₀) v) = _
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]
      exact hT4
  intro x hx
  let x' : dualWeyl ℚ (p + q) (p + q) ν := ⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩
  have hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν) := ⟨x, hx, rfl⟩
  have h5 := Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')
  rw [smul_comm, ← hS₀] at h5
  have h6 : z • S₀ x' = x' := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]; rfl
  rw [h6] at h5
  obtain ⟨y, hy, hyx⟩ := h5
  have h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x := by
    apply map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)
    change intQ _ _ y = intQ _ _ _
    rw [hyx, map_smul, map_smul]
    rfl
  exact h7 ▸ hy

theorem ExCut₂ (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (hD : BetaDen) : Formalism.CohomologicalDescent.E.ExCut := by
  intro N lam hlam l hl lo w hU a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l =
      exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l := by rintro c rfl; rfl
  rw [hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]
  have hA1 : Antitone (LD.res a lam) := fun i j hij =>
    hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)
  have hA2 : Antitone (LD.res b (fun i => lam (a + i))) := fun i j hij =>
    hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)
  obtain ⟨m₁, hm₁, h₁⟩ := exact_z_specialization a a le_rfl _ hA1 l hl
  obtain ⟨m₂, hm₂, h₂⟩ := exact_z_specialization b b le_rfl _ hA2 l hl
  obtain ⟨m, hm, hden⟩ := hD l w hl
  have hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i := fun i j _ => by
    have h1 := (hU i i.2).2
    have h2 := (hU j j.2).1
    simp only [UnitNormBounds.UN] at h1 h2
    omega
  have hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b)) := fun i j => by
    have hpos : 0 < a + b := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
    have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])
    have h3 := hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)
    simp only [LD.res] at h1 h2 h3 ⊢
    omega
  have hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · omega
    · have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
      have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])
      simp only [LD.res] at h1 h2
      omega
  have key := cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden
  refine Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · exact hm₁ h
      · exact hm₂ h
    · exact hm (hl.dvd_of_dvd_pow h)
  · convert key x hx using 3
    rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]
    ring

theorem exCut : Formalism.CohomologicalDescent.E.ExCut :=
  ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two GlobalTheory.T.rank_one_projector_weight_zero_invariance GlobalTheory.T.rank_two_consecutive_projector_invariance) GlobalTheory.T.adjoint_action_endomorphism_weight_bound (GlobalTheory.T.projectorGridScalar_of_projectorScalar GlobalTheory.T.projector_value_highest_weight_vector) GlobalTheory.T.projector_grid_denominator_bound
    GlobalTheory.T.dualWeylModuleStructureGl_proof GlobalTheory.T.dualWeylWeightSpreadBound_proof GlobalTheory.T.dualWeyl_schur_endomorphism
    (GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses (GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable) GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal GlobalTheory.T.dualWeyl_restriction_rowOperators) GlobalTheory.T.beta_integral_denominator_bound

end GlobalTheory.LeviCut
end
end
end
