module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleMinusExceptional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpenStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveMultipleDominates

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleMinusExceptionalStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_minus_exceptional : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  first | exact @_root_.GlobalTheory.TwistBelow.exists_eff_isGenerated | exact _root_.GlobalTheory.TwistBelow.exists_eff_isGenerated | (intros; apply _root_.GlobalTheory.TwistBelow.exists_eff_isGenerated <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicitiesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_cartier_with_multiplicities : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ, (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) → ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  first | exact @_root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | exact _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | (intros; apply _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorAgreementOnIsomorphism

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.PullDiv

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem exists_pullCart_agree : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H
  classical
  have : CompactSpace Y₁ := compactSpace_of_isProjOver hP
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)

  have hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ e
    have hb : Function.Injective (t ∣_ U) :=
      ((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1
    have := @hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans
      (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))
    exact congrArg Subtype.val this
  let c : Y₀ → ℤ := fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0
  have hc : ∀ w, t w ∈ U → c (t w) = H.mult w := by
    intro w hw
    have h : ∃ w', t w' = t w ∧ t w ∈ U := ⟨w, rfl, hw⟩
    simp only [c, dif_pos h]
    have e := h.choose_spec
    rw [hinj _ _ (by rw [e.1]; exact hw) hw e.1]
  have hsupp : Function.support c ⊆ t '' Function.support H.mult := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      exact ⟨w, by simpa [hc w hw] using hz, rfl⟩
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  have hfin : (Function.support c).Finite := (H.finite_support_mult.image _).subset hsupp
  have hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1 := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      rw [hc w hw] at hz
      rw [← (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU w hw).1]
      exact CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod
  refine ⟨H₀, fun y hy hmem => ?_⟩
  have : GlobalTheory.IsNormalScheme Y₁ := (isNormalScheme_iff Y₁).mpr fun x =>
    ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x
      UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  obtain ⟨z, hzy, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem
  have hzU : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  apply hz
  have hm := CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z
  rw [sub_add_cancel, (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU] at hm
  omega

end GlobalTheory.PullDiv
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorAgreementOnIsomorphismStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_agreement_on_isomorphism : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  first | exact @_root_.GlobalTheory.PullDiv.exists_pullCart_agree | exact _root_.GlobalTheory.PullDiv.exists_pullCart_agree | (intros; apply _root_.GlobalTheory.PullDiv.exists_pullCart_agree <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveMultipleDominatesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_multiple_dominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  first | exact @_root_.GlobalTheory.effDominates | exact _root_.GlobalTheory.effDominates | (intros; apply _root_.GlobalTheory.effDominates <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelative

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.AmpleUpstairs


open GlobalTheory.Cartier.CartierDiv in
theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) : (-D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.neg.mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_inv_eq_inv_val]
  exact hu.inv


open GlobalTheory.Cartier.CartierDiv in
theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) (m : ℕ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [(hg.nsmul m).mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ j : ℕ, UnitAt x ((g : X.functionField) ^ j) := by
    intro j
    induction j with
    | zero => simpa using unitAt_one x
    | succ j ih => rw [pow_succ]; exact ih.mul hu
  exact key m

end GlobalTheory.AmpleUpstairs

namespace GlobalTheory


open GlobalTheory.AmpleUpstairs in
theorem exists_ample_pull_sub_eff : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hq ht I hiso hI A hA
  obtain ⟨-, L₁, hL₁⟩ := isProper_and_exists_isAmpleLB_of_isProjOver ht
  haveI : CompactSpace Y₁ := hL₁.compactSpace
  haveI : CompactSpace Y₀ := hA.compactSpace
  haveI : IsNoetherian Y₀ := {}
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y₁ := GlobalTheory.ModifSections.isNormalScheme_of_smooth (t ≫ q)
  obtain ⟨H, hH⟩ := toPic_surjective (cls L₁ hL₁.isLB)
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.divisor_agreement_on_isomorphism k Y₀ Y₁ q n t ht I.support.compl hiso H
  obtain ⟨E₀, hE₀, hsE₀, hgen⟩ := GlobalTheory.T.blowup_ample_minus_exceptional Y₀ Y₁ t I hI A hA
  have hD : (H - pullCart t H₀).supp ≤ E₀.supp := by
    intro y hy
    rw [hsE₀, Scheme.IdealSheafData.support_comap]
    by_contra h
    exact hH₀ y h hy
  obtain ⟨e, he⟩ := GlobalTheory.T.effective_multiple_dominates Y₁ (H - pullCart t H₀) E₀ hE₀ hD
  obtain ⟨c₁, hc₁, hc₁'⟩ :=
    ((hA.eventually_isGenerated_tens_lbPow (isLB_toLB (-H₀))).and (eventually_ge_atTop 1)).exists
  obtain ⟨c₂, hc₂⟩ := hgen.exists
  obtain ⟨P, hP, hPc⟩ := cls_surj (c₂ • CechPic.pull t (cls A hA.isLB) - toPic E₀)
  have gP := hc₂ P hP hPc
  have g₁ := hc₁.pull t
  have gM := AmpleModelPos.isGenerated_tens g₁ (gP.pow e)
  have hA₁L := isLB_tens hL₁.isLB gM.isLB
  have hA₁ : IsAmpleLB (tens L₁ (tens ((tens (toLB (-H₀)) (lbPow A c₁)).pull t) (lbPow P e))) := by
    refine hL₁.tensor_isGenerated gM hA₁L ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB, cls_div hA₁L hL₁.isLB, cls_tens hL₁.isLB gM.isLB]
    abel
  refine ⟨c₁ + e * c₂, e • E₀ - (H - pullCart t H₀), _, hA₁, by omega, he, ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (GlobalTheory.Cartier.CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hsE₀.le) ?_)
    exact (supp_neg_le _).trans (hD.trans hsE₀.le)
  · rw [cls_tens hL₁.isLB gM.isLB, cls_tens g₁.isLB (gP.pow e).isLB,
      cls_lbPow hP e, hPc, cls_pull (isLB_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁)) t,
      cls_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁), cls_lbPow hA.isLB c₁, ← toPic_apply,
      map_sub, map_nsmul, map_sub, toPic_pullCart, hH, map_add, map_neg, map_nsmul, add_smul, mul_smul]
    simp only [map_neg, smul_sub]
    abel

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelativeStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_relative : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  first | exact @_root_.GlobalTheory.exists_ample_pull_sub_eff | exact _root_.GlobalTheory.exists_ample_pull_sub_eff | (intros; apply _root_.GlobalTheory.exists_ample_pull_sub_eff <;> assumption)
end
end
