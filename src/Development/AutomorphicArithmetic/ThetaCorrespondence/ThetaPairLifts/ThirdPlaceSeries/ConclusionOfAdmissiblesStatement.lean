module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAllStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutBoundOfSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtin
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.PadicSubsetSums.StableGradedCounts.PadicValCardGL
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.LocalCongruenceBound
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissible

theorem fontaineProperties_all_places : ∀ D : D7, Formalism.MainNotions.PairedCharacterCondition.FontaineAtPlacesOverL (D := D) := by
  intro D l _ K LL
  exact GlobalTheory.FontaineAll.fontaineAt_all D l K LL

end GlobalTheory.FontaineAdmissible
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.TypePrimeEta

theorem sum_two_mul_Icc (r : ℕ) : ∑ a ∈ Finset.Icc 1 r, 2 * a = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem padicValNat_pow_sub_one_le (g g' a : ℕ) (hg : g.Prime) (hg' : 2 ≤ g') (hgg : g' ≤ g ^ 2)
    (ha : 1 ≤ a) : padicValNat g (g' ^ a - 1) ≤ 2 * a := by
  haveI : Fact g.Prime := ⟨hg⟩
  have h1 : 1 < g' ^ a := Nat.one_lt_pow (by omega) (by omega)
  have hpos : 0 < g' ^ a - 1 := by omega
  have hle : g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := Nat.le_of_dvd hpos (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hlt : g ^ padicValNat g (g' ^ a - 1) < g ^ (2 * a) := by
    calc g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := hle
      _ < g' ^ a := by omega
      _ ≤ (g ^ 2) ^ a := Nat.pow_le_pow_left hgg a
      _ = g ^ (2 * a) := by rw [← pow_mul]
  by_contra h
  have h := Nat.lt_of_not_le h
  have := Nat.pow_le_pow_right hg.pos h.le
  omega

theorem val_card_le (g g' r f : ℕ) (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g')
    (hgg : g' ≤ g ^ 2) :
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g)) ^ f *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g')) ^ f) ≤ 2 * f * r ^ 2 := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : Fact g'.Prime := ⟨hg'⟩
  have h0 : ∀ q : ℕ, [Fact q.Prime] → Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) ≠ 0 :=
    fun q _ => Nat.card_pos.ne'
  obtain ⟨h1, h2⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.padicValCardGeneralLinear g g' r hne
  have hpow (a n : ℕ) : padicValNat g (a ^ n) = n * padicValNat g a := by
    simpa only [← Nat.padicValNat_def] using (Nat.multiplicity_pow (p := g) a n)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ (h0 g)) (pow_ne_zero _ (h0 g')), hpow, hpow, h1, h2]
  have hs : ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) ≤ r * (r + 1) := by
    rw [← sum_two_mul_Icc]
    exact Finset.sum_le_sum fun a ha =>
      padicValNat_pow_sub_one_le g g' a hg hg'.two_le hgg (Finset.mem_Icc.1 ha).1
  have hd : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have he : r * (r - 1) + r * (r + 1) = 2 * r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  calc f * (r * (r - 1) / 2) + f * ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)
      ≤ f * (r * (r - 1)) + f * (r * (r + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hs)
    _ = 2 * f * r ^ 2 := by rw [← mul_add, he]; ring

theorem val_cardG0g_le (D : D7) (k k' : Fin 2) (hkk : k ≠ k')
    (hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)) :
    padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ≤ 2 * D.R.f * D.R.r ^ 2 := by
  have hg := D.host.g_prime k
  have hg' := D.host.g_prime k'
  have hgg : D.host.g k' ≤ D.host.g k ^ 2 := by
    have h1 : (0 : ℝ) < D.host.g k' := by exact_mod_cast hg'.pos
    have h0 : (0 : ℝ) < (D.host.g k : ℝ) ^ 2 := pow_pos (by exact_mod_cast hg.pos) 2
    have h2 : Real.log (D.host.g k' : ℝ) ≤ Real.log ((D.host.g k : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have := (Real.log_le_log_iff h1 h0).1 h2
    exact_mod_cast this
  have hk : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
    fin_cases k <;> fin_cases k' <;> simp_all
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne hgg
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_comm]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne.symm hgg

theorem first_le (f r t CT N r' e n : ℕ) (C : ℝ) (hC : 8 * (CT : ℝ) ≤ C) (hN2 : 2 ≤ N)
    (hN : N ≤ n + 1) (hr4 : 4 * r' ≤ N ^ 2) (hn : r + t = n) :
    ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ) ≤
      4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
  have hn1 : (1 : ℝ) ≤ n := by have : 1 ≤ n := by omega
                               exact_mod_cast this
  have hnR : (n : ℝ) = r + t := by rw [← hn]; push_cast; ring
  have a1 : (4 : ℝ) * r' ≤ (N : ℝ) ^ 2 := by exact_mod_cast hr4
  have a2 : (N : ℝ) ≤ 2 * n := by
    have : N ≤ 2 * n := by omega
    exact_mod_cast this
  have a0 : (0 : ℝ) ≤ N := by positivity
  have a3 : (N : ℝ) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ a0 a2 2
  have hNr : 4 * ((N : ℝ) * r') ≤ 4 * (2 * (n : ℝ) ^ 3) := by
    calc 4 * ((N : ℝ) * r') = N * (4 * r') := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left a1 a0
      _ = N ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := pow_le_pow_left₀ a0 a2 3
      _ = 4 * (2 * (n : ℝ) ^ 3) := by ring
  have hs : (N : ℝ) + r' ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have he0 : (0 : ℝ) ≤ e := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ r' := by positivity
  have hm : ((e : ℝ) + t + 1) * (N + r') ≤ ((e : ℝ) + t + n) * (3 * (n : ℝ) ^ 2) :=
    mul_le_mul (by linarith) hs (by positivity) (by positivity)
  have hX : (N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r') ≤ 5 * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [pow_nonneg (show (0:ℝ) ≤ n by linarith) 2]
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) + e + t) := by positivity
  have hCT : (0 : ℝ) ≤ CT := by positivity
  have hCX : (CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r')) ≤
      C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hCT, mul_le_mul_of_nonneg_right hC hY]
  calc ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ)
      = 4 * (f : ℝ) * n * ((CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r'))) := by
        push_cast; rw [hnR]; ring
    _ ≤ 4 * (f : ℝ) * n * (C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t))) :=
        mul_le_mul_of_nonneg_left hCX (by positivity)
    _ = 4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by ring

end GlobalTheory.TypePrimeEta

namespace GlobalTheory

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeBoundOfEtaBound

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.TypePrimeEta
end GlobalTheory.TypePrimeEta
namespace GlobalTheory
theorem typePrimeBound_of_etaBound_alt : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissibles

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory
theorem conclusion_of_typeLocus_alt {D : D7} (P : Pend D) (CT : ℕ)
    (hcut : ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs)
    (hl5 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π)) :
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := by
  intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hQ := hl5 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hc := hcut i k hl
  choose! Xs β b hcb using hc
  refine ⟨Xs, β, b, fun π hπ => ⟨(hcb π hπ).1, ?_⟩⟩
  exact hQ π hπ (Xs π) (hcb π hπ).1.1 (hcb π hπ).2
theorem admT_of_adm5_eigSpan_tieInePoly : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR D P HW F C CT hC hadm5 hEig hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hSer hTB hBK hBC hLGC htie0 htieChi
  have hSteps : _root_.GlobalTheory.Pass.NoCutStatement := _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt hGAR
  have hCent : CentralElt D := hSteps.2.1 hSteps.1 D P
  have hl5 := _root_.GlobalTheory.Pass.cutBound_of_steps_alt hSteps D P HW F CT hadm5 (GlobalTheory.Per.ResFinite.adm12_elementDenominator D) hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB
    hBK hBC hLGC (GlobalTheory.FontaineAdmissible.fontaineProperties_all_places D) htie0 htieChi
  have hcut := _root_.GlobalTheory.T.admBC_of_serLoc D P hSer hBC hLGC htie0 hadm5 hEig hCent
  have h3 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := _root_.GlobalTheory.conclusion_of_typeLocus_alt P CT hcut hl5
  have h4 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) := by
    intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8
    exact GlobalTheory.EtaFromCut.etaBound_of_cut D CT i k ρ eta
      (h3 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8)
  exact _root_.GlobalTheory.typePrimeBound_of_etaBound_alt D C CT hC h4
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissiblesStatement

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  first | exact @_root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | exact _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | (intros; apply _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly <;> assumption)
end
end
end
