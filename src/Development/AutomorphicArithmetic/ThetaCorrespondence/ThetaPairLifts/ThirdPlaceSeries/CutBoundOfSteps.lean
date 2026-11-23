module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateTwistMultiplicationIntertwines
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultVTwistedDual

section

@[expose] public section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.DualJump

open GlobalTheory.DRFil GlobalTheory.DRDual

theorem multV_twisted_dual {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V')
    (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ) (hm : Function.Bijective m)
    (hg : ∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y)
    (h : IsDR (P.PD K) ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  have := K.2
  have := LL.2
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨-, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  obtain ⟨n, d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

theorem dualJumpL : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → DualJumpL L := by
  intro L AI hT l _ K LL A A' m hm h τ a
  obtain ⟨T⟩ := hT l
  obtain ⟨hg, h1, -, hd⟩ := hm
  have hi : Function.Injective m :=
    (injective_iff_map_eq_zero m).2 fun x hx => h1 x fun y => by rw [hx, LinearMap.zero_apply]
  have hb : Function.Bijective m :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := ↥LL.1) (V := A'.V)).symm)).1 hi⟩
  have key := multV_twisted_dual T K LL A.ρ A'.ρ m 1 hb (fun g x y => by rw [zpow_one]; exact hg g x y) h τ (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at key
  rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A'.V A'.ρ τ a).2.2,
    (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A.V A.ρ τ (-a - 1)).2.2, key]

end GlobalTheory.DualJump
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotDRLOfTied

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem potDRL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PotDRL L := by
  intro L A hT l _ K K' LL h R hc
  obtain ⟨T⟩ := hT l
  exact (GlobalTheory.T.restrict_crystalline_deRham_finiteExt l (L l) (A l) T K K' LL h R.V R.ρ).2.2
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (L l) (A l) T K' LL R.V _ hc).1

end GlobalTheory.Pass
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodParIffGoodSig

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutBoundOfSteps

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
noncomputable section
namespace GlobalTheory.Pass


theorem cutBound_of_steps_alt : _root_.GlobalTheory.Pass.NoCutStatement → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i))
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith
end GlobalTheory.Pass
end
end
end
end
