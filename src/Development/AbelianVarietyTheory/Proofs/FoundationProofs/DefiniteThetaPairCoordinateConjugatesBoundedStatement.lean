module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPointsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPointsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestVectorAdelicPairTranslatesMovedLatticeVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLeStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateJetBoundVacuumTorsionTranslate

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.jet

theorem jet_bound_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (hGT : G ∈ Th D (tor0 D cc δ) L L')
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (n : D.what₂.Tau → ℕ) (B : ℝ) (hB : 1 ≤ B) (hn : ∀ τ, (n τ : ℝ) ≤ 2 * B)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) (T : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
    ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤
      ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 *
        (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
          normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) *
          (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  have hg1 : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2 Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hg1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.T.galois_data_exists D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
    (by omega)
  have hgal := (GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [GlobalTheory.ConjJet.comb_one]; exact hA)
    (by rw [GlobalTheory.ConjJet.comb_one]; exact hAU y hy)).1
  rw [GlobalTheory.ConjJet.comb_one] at hgal
  have hdiff := GlobalTheory.ConjJet.U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1
  obtain ⟨hmem, hcj⟩ := (GlobalTheory.ConjSeries.taylor_fnConj D a d Qbar ρ (U D (tor0 D cc δ) y G)
    (by rw [hgal]; exact hdiff) (by rw [hgal]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ hne)).2 (hAU y hy) n T
  refine ⟨hmem, ?_⟩
  rw [hcj, hgal]
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  refine (GlobalTheory.MinorBound.minor_bound D a d n _ _ (area (lamConj Qbar ρ (lamOf D cc δ))) B
    (by rw [hΛ]; exact GlobalTheory.ConjJet.area_pos D hg1 cc' δ' hc') hB ?_ hn hdiff fun z => ?_).2 T
  · have := GlobalTheory.ConjJet.normSq_nonneg D (torConj D (tor0 D cc δ) Qbar ρ)
      (La D (torConj D (tor0 D cc δ) Qbar ρ) L L') (fnConj D Qbar ρ G)
    positivity
  · have := GlobalTheory.ConjJet.sup_perm D hg1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh y' z
    rw [GlobalTheory.ConjJet.Hf_re, ← mul_div_assoc] at this
    exact this

theorem vacuum_mem_thetaSpace_pair (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_jet_bound : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  intro D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy n B hB hn ρ t0' ht' T
  have hGT := vacuum_mem_thetaSpace_pair D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t0' ht'
  rw [← hN]
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc Qbar ρ hdata
  · exact jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB hn ρ hfix T
  · obtain ⟨hmem, hle⟩ := jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB
      hn (rhoBar Qbar ρ) hfix T
    refine ⟨hmem, ?_⟩
    obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [GlobalTheory.ConjJet.U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [GlobalTheory.ConjJet.cj_bar, (hbar a d L L' G).1, htor, hn2, hL, GlobalTheory.ConjJet.area_conj] at hle
    exact hle

end GlobalTheory.ArchFree.jet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateJetBoundVacuumTorsionTranslateStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.conjugate_jet_bound_vacuum_torsion_translate : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  first | exact @GlobalTheory.ArchFree.jet.conj_jet_bound | exact GlobalTheory.ArchFree.jet.conj_jet_bound | (intros; apply GlobalTheory.ArchFree.jet.conj_jet_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumImageIntertwinerSelfDualPair

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.firstBasisVectorLike

open GlobalTheory.VacuumMove

theorem isVacuum_thetaIntertwiner_selfDual : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  rintro D cc δ t0 hc ht a d L L' L₁ L₁' hL hL' hL₁ hL₁' G ⟨b, κ, hb, hκ, rfl⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.T.admissible_characters_exist D cc δ hc a d _ _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩)
    (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _ (pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨b, κ * μ, hb, mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

end GlobalTheory.ArchFree.firstBasisVectorLike
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumImageIntertwinerSelfDualPairStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  first | exact @GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | exact GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | (intros; apply GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBounded

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.coord

theorem coord_conj_le : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact GlobalTheory.T.conjugate_jet_bound_vacuum_torsion_translate D cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum D cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair D cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := GlobalTheory.NormSum.CoordConj.differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, GlobalTheory.NormSum.CoordConj.applyAt0_comb _ _ _ fun i => GlobalTheory.NormSum.CoordConj.differentiable_U _ hGd]
    refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.ArchFree.coord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBoundedStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.ArchFree.coord.coord_conj_le | exact GlobalTheory.ArchFree.coord.coord_conj_le | (intros; apply GlobalTheory.ArchFree.coord.coord_conj_le <;> assumption)
end
end
