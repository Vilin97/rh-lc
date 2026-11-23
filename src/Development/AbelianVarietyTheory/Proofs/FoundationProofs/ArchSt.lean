module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelbergStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOneStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBounded

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.means

open GlobalTheory.PositiveMeans

theorem exists_crv_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 (lamOf D cc δ) ∈ M) (h3 : g3 (lamOf D cc δ) ∈ M) :
    ∃ cc' δ', Crv D cc' δ' ∧ lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ' := by
  obtain ⟨M', ρ', halg, hext⟩ := GlobalTheory.TwoTorsionPt.exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    exact ⟨cc', δ', hc', e⟩
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    have hm : (lamConj M' ρ' (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc' δ' := by
      rw [← e]
      exact (congrArg Tor.abelian₂ hbar).symm
    generalize lamConj M' ρ' (lamOf D cc δ) = Λ at hm
    obtain ⟨-, -, hdisc, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    have hd : TaylorLogMetric.discr Λ = 1 := by
      rw [← hm, TaylorLogMetric.discr, g2, g3, eisG_conj, eisG_conj] at hdisc
      apply (starRingEnd ℂ).injective
      rw [map_one, ← hdisc, TaylorLogMetric.discr, g2, g3]
      simp [map_ofNat]
    obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ)
      (by rw [hd]; exact one_ne_zero)
    obtain ⟨c, d, h, -, e'⟩ := GlobalTheory.ConjCurve.exists_crv D Λ L.ω₁ L.ω₂ (by simpa using L.indep.ne_zero 0)
      (fun z => (hL z).trans PeriodPair.mem_lattice) (fun r z hz => by
        obtain ⟨r', hr⟩ := exists_conj D r
        have h1 : (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hm ▸ ⟨z, hz, rfl⟩
        have h4 : GlobalTheory.ConjCurve.embK D r' * (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hO r' _ h1
        rw [hr, ← map_mul, ← hm] at h4
        obtain ⟨u, hu, e⟩ := h4
        have : u = _ := (starRingEnd ℂ).injective e
        exact this ▸ hu) hd 1 one_pos
    exact ⟨c, d, h, e'⟩

theorem means_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  obtain ⟨C, hC, hA⟩ := GlobalTheory.LatticeAreaBound.area_bounded_of_discr_eq_one
  have hc1 : 0 ≤ Real.posLog C := Real.posLog_nonneg
  have hc2 : 0 ≤ Real.posLog (2 * Real.pi ^ 2) := Real.posLog_nonneg
  refine ⟨18 + 3 / 2 * (Real.posLog (2 * Real.pi ^ 2) + (Real.posLog C + 2)), by positivity, ?_⟩
  intro D cc δ t0 hc _ L hL hrd hdl M _ h2 h3 _ t ht
  obtain ⟨-, hlogd, hr1, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.InducedType.induced_type D).1
  have hn : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = Module.finrank ℚ M := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hper := GlobalTheory.T.mean_log_period_conjugates_eq_chowlaSelberg D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M h2 h3
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hpi := Real.pi_gt_three
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
  have hl2p : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le, div_eq_iff hn.ne'] at hper
  have hB : Real.posLog (3 * (2 * D.host.rdE + 1)) ≤ 9 * L := by
    refine (Real.posLog_le_posLog (by linarith) (show _ ≤ 9 * D.host.rdE by linarith)).trans ?_
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith),
      Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num)
    linarith
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
        Real.posLog C - Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi) - Real.log Real.pi ∧
      Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) ≤
        (18 * L + 3 / 2 * Real.posLog (2 * Real.pi ^ 2)) +
          3 / 2 * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := by
    intro ρ
    obtain ⟨cc', δ', hc', e⟩ := exists_crv_conj hc M ρ h2 h3
    have ht' := ht ρ
    rw [e] at ht' ⊢
    obtain ⟨hΛ, -, hdisc, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    obtain ⟨ha0, haC⟩ := hA _ hΛ hdisc
    constructor
    · rw [Real.log_div ha0.ne' (by positivity)]
      have h1 := Real.posLog_le_posLog (by linarith) haC
      have h4 := Real.posLog_sub_posLog_inv (x := area (lamOf D cc' δ'))
      linarith
    · have := posLog_nrm_le _ hΛ hdisc ((GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).1 cc' δ' hc'.1 hc'.2)
        (GlobalTheory.T.sigmaStar_value_le_meanSquare_genusOne D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc') ht'.1 (not_mem_lattice_of_isCMTorsionBasePoint ht' hO)
      linarith
  have s1 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
      (Real.posLog C + 2) * L * Module.finrank ℚ M := by
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).1).trans ?_
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hper, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard]
    have h5 := le_abs_self (logDerivativeAtOne D)
    have h6 : Real.posLog C ≤ Real.posLog C * L := le_mul_of_one_le_right hc1 hL
    have h7 : Real.posLog C - (Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log D.host.d / 2) -
      logDerivativeAtOne D) - Real.log Real.pi ≤ (Real.posLog C + 2) * L := by linarith
    have := mul_le_mul_of_nonneg_right h7 hn.le
    linarith
  have h8 : Real.posLog (2 * Real.pi ^ 2) ≤ Real.posLog (2 * Real.pi ^ 2) * L := le_mul_of_one_le_right hc2 hL
  constructor
  · rw [div_le_iff₀ hn]
    refine s1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hn.le)
    linarith
  · rw [div_le_iff₀ hn]
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).2).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have := mul_le_mul_of_nonneg_right h8 hn.le
    linarith

end GlobalTheory.ArchFree.means
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBoundedStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  first | exact @GlobalTheory.ArchFree.means.means_le | exact GlobalTheory.ArchFree.means.means_le | (intros; apply GlobalTheory.ArchFree.means.means_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormMeanInfPosLogLeDefiniteThetaPair

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.norm

open GlobalTheory.ArchNorm



theorem norm_meanInf_posLog_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded
  refine ⟨1100 + 4 * C₀, by positivity, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ N B L P x hN hB hL hrL hdL hsm hx
  obtain ⟨-, -, hr, hf, hcard, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨-, hcd, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D P.d
  obtain ⟨hfin, hch⟩ := hJ P.J P.J_le P.idx_ne
  have hca := (GlobalTheory.NormSum.cls_finite_card_le D P.a).2.1
  have hcT := (GlobalTheory.MinorBound.minor_bound D P.a P.d P.n (fun _ => 0) 0 1 B one_pos hB le_rfl hsm.2
    (differentiable_const _) (fun z => by simp)).1
  have hcoord := GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded D cc δ t0 Q hc ht P hQ B hB hsm.2
  let _ : Fintype (Cls D P.d P.J) := Fintype.ofFinite _
  have hwp : wpF (lamOf D cc δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := mul_mem_lamOf D cc δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have hz : ∀ h T, P.coord h T ∈ Qbar := fun h T => by
    obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar Qbar.val hdata.2.1 hdata.2.2
    exact (hcoord Qbar.val t' ht' h T).1
  let b := Module.finBasis ℚ K
  obtain ⟨M, hM1, hM2, hM⟩ := exists_galois
    (Set.range (fun i => σ (b i)) ∪
      Set.range (fun p : Cls D P.d P.J × Tup D P.a P.d P.n => P.coord p.1.out p.2) ∪
      {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wpF (lamOf D cc δ) t0})
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.toFinite _)) (by
      rintro y ((⟨i, rfl⟩ | ⟨p, rfl⟩) | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom σ.toRatAlgHom)
      · exact hz _ _
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, σ y ∈ M := fun y => by

    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : g2 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h3 : g3 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h4 : wpF (lamOf D cc δ) t0 ∈ M := hM _ (Or.inr (by simp))
  have hzM : ∀ p : Cls D P.d P.J × Tup D P.a P.d P.n, P.coord p.1.out p.2 ∈ M :=
    fun p => hM _ (Or.inl (Or.inr ⟨p, rfl⟩))
  choose t htt using fun ρ : M →ₐ[ℚ] ℂ => (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 M ρ h2 h3
  obtain ⟨hu, hv⟩ := hmean D cc δ t0 hc ht L hL hrL hdL M h2 h3 h4 t htt
  refine (GlobalTheory.ArchMean.meanInf_posLog_le K σ x M (Cls D P.d P.J × Tup D P.a P.d P.n)
    (fun p => ((gam D P.J p.1.out : ℚ))⁻¹) (fun p => ⟨P.coord p.1.out p.2, hzM p⟩) hσ
    (fun p => by positivity) ?_).trans ?_
  · rw [hx, Pair.norm, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Pair.sq, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hs : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ 2 * fF D * B := by
    push_cast
    refine (Finset.sum_le_card_nsmul _ _ _ fun τ _ => hsm.2 τ).trans (le_of_eq ?_)
    rw [Finset.card_univ, hcard, nsmul_eq_mul]; ring
  have hf' : (1 : ℝ) ≤ fF D := by exact_mod_cast hf
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 ≤ Real.log (B * (2 * (N : ℝ))) := Real.log_nonneg (by nlinarith)
  have hfn : 1 ≤ (fF D : ℝ) * (2 * (N : ℝ)) := by nlinarith
  have hl0 : 0 ≤ Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := Real.log_nonneg (by nlinarith)
  have hq0 : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  set E₀ : ℝ := 1100 * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
      1100 * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) +
      1100 * (N : ℝ) ^ 2 * Real.log Q with hE₀
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (∑ p : Cls D P.d P.J × Tup D P.a P.d P.n,
        ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) * ‖ρ ⟨P.coord p.1.out p.2, hzM p⟩‖ ^ 2) ≤
      E₀ + (4 * fF D * (N : ℝ) ^ 2 * Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) +
        4 * fF D * N * B * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) := by
    intro ρ
    obtain ⟨ρ', hρ⟩ := exists_extension M ρ
    have hl : lamConj Qbar ρ' (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ) := by
      unfold lamConj
      rw [hρ _ h2, hρ _ h3]
    have hb := hcoord ρ' (t ρ) (hl ▸ htt ρ)
    rw [hl] at hb
    have h5 : 0 ≤ Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) := Real.posLog_nonneg
    have h6 : 0 ≤ Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := Real.posLog_nonneg
    refine posLog_le_of_le_exp (by positivity) (by positivity) (le_trans ?_
      (sizes (fF D) N P.a P.d (∑ τ, P.n τ) Q (Nat.card (Cls D P.d P.J)) (Fintype.card (Tup D P.a P.d P.n))
        _ _ B L D.host.rdE _ _ hf hN P.a_le hsm.1 hs hQ hB hL hr hrL (lattice_unitNormSq_nonneg _ _) (area_nonneg _)
        (hch.trans (Nat.mul_le_mul_left _ P.idx_le)) hcT hcd hca))
    refine sum_prod_le _ _ fun p => ?_
    · refine le_trans ?_ (hb p.1.out p.2).2
      have hg := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le p.1.out).1
      have hg1 : ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 := by
        push_cast
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg)
      have he : cj Qbar ρ' (P.coord p.1.out p.2) = ρ ⟨P.coord p.1.out p.2, hzM p⟩ := by
        unfold cj
        rw [hρ _ (hzM p)]
        unfold TaylorLogMetric.liftM
        rw [dite_eq_left (hzM p)]
      rw [he]
      exact mul_le_of_le_one_left (by positivity) hg1
  clear_value E₀
  have hM0 : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun ρ _ => key ρ) hM0.le).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, AlgHom.card, nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hM0.ne',
    mul_div_assoc, mul_div_assoc]
  have p1 := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 * fF D * N * B by positivity)
  have p2 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 4 * fF D * (N : ℝ) ^ 2 by positivity)
  have p3 : 0 ≤ C₀ * fF D * N * B * L := by positivity
  have p4 : 0 ≤ C₀ * fF D * N * B * Real.log (B * (2 * (N : ℝ))) := by positivity
  have p5 : 0 ≤ C₀ * fF D * (N : ℝ) ^ 2 * Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := by positivity
  have p6 : 0 ≤ C₀ * (N : ℝ) ^ 2 * Real.log Q := by positivity
  rw [hE₀]
  linarith

end GlobalTheory.ArchFree.norm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormMeanInfPosLogLeDefiniteThetaPairStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.norm_meanInf_posLog_le_definiteThetaPair : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  first | exact @GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le | exact GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le | (intros; apply GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchSt

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.st

theorem archSt : ArchSt := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.T.norm_meanInf_posLog_le_definiteThetaPair
  refine ⟨C, hC, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ ι N B L P P' zA zA' hN hB h1 hL hd hs hn i
  exact ⟨h D cc δ t0 Q hc ht hQ K σ N B L (P i) (zA i) hN hB h1 hL hd (hs i).1 (hn i).1,
    h D cc δ t0 Q hc ht hQ K σ N B L (P' i) (zA' i) hN hB h1 hL hd (hs i).2 (hn i).2⟩

end GlobalTheory.ArchFree.st
end
end
