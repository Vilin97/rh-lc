module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimateStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentWeightedStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistancesStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModular
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowth
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBound
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursion
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLeStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVector

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdGap

theorem product_moment_first_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν hNz
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hG, -, -, -⟩ := hH
  have hKS : PI.KFinSmooth := by
    unfold BranchingSupport.HypsG BranchingSupport.InputsG at hG
    exact hG.1.2.2.1
  obtain ⟨hN, hFam, hSd, hSF⟩ := hS
  have hk : 1 ≤ k := by
    unfold BranchingSupport.Num at hN
    exact hN.1
  have hz : Formalism.QuantumDeterminants.inWb k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.1
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.2.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  have hDS : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    unfold BranchingSupport.IsFam at hFam
    exact hFam ν' h'
  have hDG : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    have h2 := hSG
    unfold BranchingSupport.SetupG BranchingSupport.IsFamG at h2
    exact h2.2.1 ν' h'
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := by
    unfold PI.UpqRep.IsCayleyU at hQ
    exact ⟨⟨Q, star Q, Matrix.mem_unitaryGroup_iff.mp hQ.2, Matrix.mem_unitaryGroup_iff'.mp hQ.2⟩, rfl⟩
  have hEx : ∀ ν' : Fin (2 * r + k + 1) → ℤ, ∃ E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E' ∧ Formalism.REAL.GlRel E' := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E', h1, h2⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hKS k r _ _ (R ν') (hDS ν' h') Q hQu
      exact ⟨E', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hEx
  obtain ⟨w, hw1, -, hKH, hfin⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hKS k r _ _ (R ν) (hDS ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hG k r _ _ (R ν) hk (hDG ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hLev : BranchingSupport.Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w := by
    unfold BranchingSupport.IsMod at hMod
    exact GlobalTheory.lev_zero_of_kHighest _ _ _ _ _ _ hMod.1 hMod.2.1 hKH hfin
  have hq4 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have h1 : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hA : ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q) := by
    intro q hq
    have h1 := Gp91.GlobalTheory.Moment.moment_first_length hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') q ν (le_trans (Nat.add_le_add_left hq _) hν) 0 (hq4 q hq) w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hRr : ∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ /
      lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤
      ENNReal.ofReal ((b ^ 2) ^ (2 * q)) := by
    intro a q hq
    have h1 := Gp91.GlobalTheory.RatioMoment.ratio_moment hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') ν hν0 0 q (hq4 q hq) a w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hdg : 0 < dg ν := (hSF ν hν0).2.1
  have hmass : ∫⁻ x, ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ∂νq = 1 := by
    have h1 := ((Gp91.GlobalTheory.MomMass.mom_mass hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν0).2
      hNz).2 (w : (R ν).H) w.2
    simp only [one_mul] at h1
    rw [h1]
    have h2 : ‖(w : (R ν).H)‖ = 1 := hw1
    rw [h2, one_pow, ENNReal.ofReal_one]
  obtain ⟨hae, -, hlenM, hbesM⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKS k r _ _ (R ν) Wp z π u μW μN μG νq (hDS ν hν0) hSd
  obtain ⟨hIsBes, -⟩ := (hSF ν hν0).1
  have hPhM : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) νq :=
    ((hbesM (lb ν) hIsBes (w : (R ν).H) w.2).norm.aemeasurable.pow_const 2).const_mul (dg ν)
  have hpos : ∀ a, ∀ᵐ x ∂νq, 0 < lenA k r z (Matrix.of x) a := fun a =>
    hae.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hz hT (Matrix.of x) hx).2.2.1 a
  have hnf := (GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).1
  have hb1 : 1 ≤ b := by
    have h1 := hnf.2.2.1
    have h2 : (0 : ℝ) ≤ 2 * r + k := by positivity
    linarith
  have hbv : 0 ≤ bv := by linarith [hnf.2.1]
  have hA0 : 0 ≤ ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hT.le (by positivity))) (pow_nonneg (by linarith) _)
  have key := GlobalTheory.T.initial_lengths_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r l hl (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2) (fun a => hlenM a) hpos hPhM
    (fun x => mul_nonneg hdg.le (sq_nonneg _)) hmass hA0 (one_le_pow₀ hb1) hA hRr
  refine ⟨(w : (R ν).H), w.2, hw1, le_trans key (ENNReal.ofReal_le_ofReal ?_)⟩
  exact pow_le_pow_left₀ (mul_nonneg hA0 (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hN hT) l

end GlobalTheory.MomProdGap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVectorStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.productMoment_firstLengths_lowestVector : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdGap.product_moment_first_gap | exact GlobalTheory.MomProdGap.product_moment_first_gap | (intros; apply GlobalTheory.MomProdGap.product_moment_first_gap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGap

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapWedgeKappaL

theorem n1_add_eZ_le_add_card' {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective' {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hyp := hH.1
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hSG
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card' ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) l => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r l
  have hdual := fun J : Sub (2 * r + k + 1) l =>
    Gp91.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (lb ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).1 s hs) (hSF ν hν0).1 hnz J
      (lb (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) l, ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, lb ν (ev (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • lb (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) l, 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg
    ((GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS)
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.productMoment_firstLengths_lowestVector hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) l) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective'
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := Gp91.GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • lb ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • lb (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : lb (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hHs : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hHs] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).2 _ hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.GapWedgeKappaL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGapStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselExteriorPower_constant_bound_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  first | exact @GlobalTheory.GapWedgeKappaL.kappa_bound | exact GlobalTheory.GapWedgeKappaL.kappa_bound | (intros; apply GlobalTheory.GapWedgeKappaL.kappa_bound <;> assumption)
end
end
