module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureConditionStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeNegativeDefiniteEqOppositeStatement
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianSpaceSelfDualLatticeSignature

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem exists_hSpace_sigOK_sig :
    ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  intro D P Q
  refine ⟨bandSpace D (P + Q) P (P + Q), bandSpace_sigOK D (P + Q) P (P + Q) le_rfl, fun τ => ?_⟩
  show (P + Q - (P + Q - P), P + Q - P) = (P, Q)
  congr 1 <;> omega

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianSpaceSelfDualLatticeSignatureStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_hermitianSpace_with_signature : ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  first | exact @GlobalTheory.exists_hSpace_sigOK_sig | exact GlobalTheory.exists_hSpace_sigOK_sig | (intros; apply GlobalTheory.exists_hSpace_sigOK_sig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioUpPositiveLine

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolRatioUp

theorem volRatio_up : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) →
    D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  intro D hT h2 W P Q hW hWs hPQ U hU hUs
  have hUr : U.rank = P + Q + 1 := by
    have := Formalism.BasicNotions.sig_sum U hU D.host.φ₀
    rw [hUs] at this
    simp only at this
    omega
  have hWr : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hWs] at this
    exact this.symm
  obtain ⟨x, -, W', ι, -, -, hW'ok, hW's, hratio⟩ :=
    h2 U (P + 1) Q hU hUs (by omega) true (by simp)
  have hW's' : ∀ τ, W'.sig τ = (P, Q) := fun τ => by
    have := hW's τ
    simpa using this
  have hW'r : W'.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W' hW'ok D.host.φ₀
    rw [hW's'] at this
    exact this.symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D W W' hW hW'ok (by rw [hWr, hW'r])
    (fun τ => by rw [hWs, hW's'])
  have hvol : D.vol W = D.vol W' :=
    (GlobalTheory.VolIndepClosed.volIndep D).2.2 hT W W' P Q ⟨hW, hWs⟩ ⟨hW'ok, hW's'⟩ φ hφ
  rw [hvol, hratio, hUr]

end GlobalTheory.VolRatioUp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatioUpPositiveLineStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_ratio_up_positive_line : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  first | exact @GlobalTheory.VolRatioUp.volRatio_up | exact GlobalTheory.VolRatioUp.volRatio_up | (intros; apply GlobalTheory.VolRatioUp.volRatio_up <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolEqMassSelfDualRankGeTwo

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_step (D : D7) (hT : VolTie D) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D)
    (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hPQ : 2 ≤ P + Q)
    (hup : ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U = massI D (P + Q + 1)) :
    D.vol W = massI D (P + Q) := by
  obtain ⟨U, hU, hUs⟩ := GlobalTheory.T.exists_hermitianSpace_with_signature D (P + 1) Q
  have hr := GlobalTheory.T.volume_ratio_up_positive_line D hT h2 W P Q hW hs hPQ U hU hUs
  have hb := massRatio_of_definiteVolume D h2 hv (P + Q + 1) (by omega)
  have e : P + Q + 1 - 1 = P + Q := by omega
  rw [e] at hb
  rw [← hb, hup U hU hUs] at hr
  have h1 := massI_pos D (P + Q + 1)
  have h3 := massI_pos D (P + Q)
  have h4 := D.vol_pos W
  field_simp at hr
  nlinarith [hr]

theorem vol_eq_massI_of_two_le_rank : ∀ D : D7, VolTie D → Conclusion2 D → DefiniteVolumeEqMass D → ∀ (W : HSpace D.host.E) (P Q : ℕ),
    W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → D.vol W = massI D (P + Q) := by
  intro D hT h2 hv
  have h2v := volume_eq_mass_of_definite D h2 hv
  have hP1 : ∀ (W : HSpace D.host.E) (Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (1, Q)) → 2 ≤ 1 + Q →
      D.vol W = massI D (1 + Q) := by
    intro W Q hW hs hQ
    refine vol_eq_massI_step D hT h2 hv W 1 Q hW hs hQ fun U hU hUs => ?_
    have := h2v.2 U 2 Q hU hUs le_rfl
    rw [this]; congr 1; omega
  intro W P Q hW hs hPQ
  rcases Nat.lt_or_ge P 2 with hP | hP
  · interval_cases P
    · refine vol_eq_massI_step D hT h2 hv W 0 Q hW hs hPQ fun U hU hUs => ?_
      rw [hP1 U Q hU hUs (by omega)]; congr 1; omega
    · exact hP1 W Q hW hs hPQ
  · exact h2v.2 W P Q hW hs hP

end GlobalTheory.Glob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolEqMassSelfDualRankGeTwoStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vol_eq_mass_selfDual_rank_ge_two : ∀ D : D7, VolTie D → Conclusion2 D → DefiniteVolumeEqMass D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → D.vol W = massI D (P + Q) := by
  first | exact @GlobalTheory.Glob.vol_eq_massI_of_two_le_rank | exact GlobalTheory.Glob.vol_eq_massI_of_two_le_rank | (intros; apply GlobalTheory.Glob.vol_eq_massI_of_two_le_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_all_sig : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK →
    (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  intro D hT h2 W P Q hW hs
  have hv : DefiniteVolumeEqMass D := mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
    (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    rw [← hrk]
    exact hv W hW (fun τ => by rw [hs τ, hrk]; rfl)
  · by_cases h2r : 2 ≤ P + Q
    · exact GlobalTheory.T.vol_eq_mass_selfDual_rank_ge_two D hT h2 hv W P Q hW hs h2r
    · have hP : P = 0 := by omega
      have hQ1 : Q = 1 := by omega
      subst hP hQ1
      have e1 : D.vol W = D.vol (GlobalTheory.NegSpace.neg W) :=
        GlobalTheory.T.volume_negativeDefinite_eq_opposite D hT W 1 hW hs
      have hN : (GlobalTheory.NegSpace.neg W).SigOK := GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW
      have e2 : D.vol (GlobalTheory.NegSpace.neg W) = massI D (GlobalTheory.NegSpace.neg W).rank :=
        hv _ hN (fun τ => by rw [GlobalTheory.NegSpace.neg_sig, hs τ, GlobalTheory.NegSpace.neg_rank, hrk])
      rw [e1, e2, GlobalTheory.NegSpace.neg_rank, hrk]

end GlobalTheory.Glob
end
end
