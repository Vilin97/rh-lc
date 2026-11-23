module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDepthZeroFixedVector
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisBlockTypeSplit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem rootsBar_mul (a b : (ZMod g)[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar (a * b) = Formalism.CyclotomicNorms.rootsBar a + Formalism.CyclotomicNorms.rootsBar b := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, Polynomial.roots_mul]
  have hi : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  exact mul_ne_zero ((Polynomial.map_ne_zero_iff hi).2 ha) ((Polynomial.map_ne_zero_iff hi).2 hb)

theorem rootsBar_pow (a : (ZMod g)[X]) (d : ℕ) : Formalism.CyclotomicNorms.rootsBar (a ^ d) = d • Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.roots_pow]

theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))),
    Polynomial.natDegree_map]

theorem rootsBar_frob (a : (ZMod g)[X]) :
    (Formalism.CyclotomicNorms.rootsBar a).map (fun x => x ^ g) = Formalism.CyclotomicNorms.rootsBar a := by
  apply GlobalTheory.TameLabels.rootsBar_frob <;> assumption

end Roots

section Lab

variable (D : D7)
  (hTw : ∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a)

include hTw

theorem inertiaCharpoly_speh_eq_pow (k : Fin 2) (w : PlE D.host) (p : BasicNotions.Part D.naut.CG) :
    D.naut.items₂ k w (spehLoc D.nd D.naut p w) = (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d := by
  have key : ∀ l : List ℝ, D.naut.items₂ k w (l.foldr (fun (j : ℝ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) =
      (D.naut.items₂ k w (D.naut.locG p.π w)) ^ l.length := by
    intro l
    induction l with
    | nil => simp [D.naut.inertiaCharpoly_zero]
    | cons j l ih => rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ, mul_comm]
  unfold spehLoc
  rw [key]
  simp

theorem inertiaCharpoly_eq_of_iso (k : Fin 2) (w : PlE D.host) (Sig : List (BasicNotions.Part D.naut.CG)) :
    D.naut.items₂ k w (isoLoc D.nd D.naut Sig w) =
      (Sig.map fun p => (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d).prod := by
  induction Sig with
  | nil => simp [isoLoc, D.naut.inertiaCharpoly_zero]
  | cons p Sig ih =>
    rw [List.map_cons, List.prod_cons, ← ih, ← inertiaCharpoly_speh_eq_pow D hTw]
    exact D.naut.inertiaCharpoly_add _ _ _ _

end Lab

end Formalism.MainNotions.N
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroEntrywise

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRow
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  intro hP hL D P hRow hLab hCen hGreen hChi
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hRow
  have hLoc : _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := _root_.GlobalTheory.DepthZeroAssembly.locDZ_of_split_reg_m_alt hL D
    (_root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero hP hL D P.ty.grp hGreen) (_root_.UpperTheory.Lit.Dz.blockTypeSplitProp hP hL D P.ty.grp hGreen)
  have hConj : ConjDual D := _root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hLab
  intro i k v PI
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro ρ f hρ hser hocc hsq hu
  have hw : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs hP hL D P hCen S hS i PI k v hw ρ f ⟨hρ, hser⟩ hocc
  obtain ⟨htame, hχ, u, hu', hlabχ⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hP hL D P hChi S hS i k v hw
  obtain ⟨hmono, hlab⟩ := hLoc k v (S i _ hw).mu hχ (u : ZMod (D.host.g k)) ((S i _ hw).rep PI) ρ f htame hlabχ
    ⟨hρ, hser⟩ hsq (hu u hu') ⟨x, hx⟩
  have hrc : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ ((S i _ hw).rep PI) = P.T.e _ (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [← hS.rc i _ hw]
    exact ((S i _ hw).locV PI).symm
  have hm0 : D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [hrc] at hmono
    exact (P.T.mono0 _ _).2 hmono
  have hl : D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t := by
    rw [P.lab k v, ← hlab]
    unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
    rw [hrc]
  have hf0 : D.ntypes.eSer k f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hser
    exact GlobalTheory.SerOSys.ZSum.zIdem_ne_zero ρ hρ hser.symm
  have hdegf : f.natDegree = D.R.r := by
    by_contra hne
    exact hf0 (D.ntypes.eSer_zero k f fun h => hne h.2.1)
  have hfne : f ≠ 0 := by
    intro h; apply hf0; exact D.ntypes.eSer_zero k f fun h' => by rw [h] at h'; exact (h'.1.ne_zero rfl)
  have hdeg : (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t).natDegree = D.R.nV := by
    rw [natDegree_mul hfne (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_X_sub_C, hdegf, mul_one]
    rfl
  refine ⟨u, hu', hm0, hl, fun w' hc => ?_⟩
  obtain ⟨hc1, -, hc3⟩ := hConj i PI k v w' hc
  have hroots : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹) := by
    rw [hc3, hl]
  refine ⟨hc1 hm0, ?_, hroots⟩
  rw [← card_rootsBar, hroots, Multiset.card_map, card_rootsBar, hdeg]
end GlobalTheory.DepthZeroRow
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  first | exact @_root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
