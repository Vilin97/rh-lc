module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealSupportNonKlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionBigBundle
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLiftStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependentStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmpleStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardIdealRegularity
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundary

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem regAt_of_regularAt_neg_roundDown : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  intro k _ _ X _ _ _ p n hproj _ Δ η m G Y _ _ s _ K B F hΔ hmult hres hF x f hf
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  by_cases hf0 : f = 0
  · subst hf0; exact regAt_zero x
  refine regAt_of_forall_coheight_eq_one fun z hzx hz1 => ?_
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hz1
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
  obtain ⟨w, rfl, hE'⟩ := GlobalTheory.T.divisor_point_proper_lift k X Y p s hres.bir inferInstance E' E hE'E _ hE
  obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
  have hg' := isEqn_pullCart s hg
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hmult.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  have hd := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m
    hmult.pos hres.div E' w (fnPull s g) hE' hg'
  have hd2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback k X Y p s hres.bir E' E hE'E n η hmult.ne_zero
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E g]
  have hd3 := (hmult.eqn _ g hg).discrep_eq_neg hmult.pos (specializes_refl _) hE
  have hm : (0 : ℚ) < m := by exact_mod_cast hmult.pos
  have hnn : 0 ≤ (pullCart s G - m • K).mult w := by
    have e : ((pullCart s G - m • K).mult w : ℚ) / m = Δ (s w) := by
      rw [← hd2, hd] at hd3
      rw [neg_div] at hd3
      exact neg_injective hd3
    have h0 : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) / m := e ▸ hΔ (s w)
    have := (div_nonneg_iff.1 h0)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.2 hm)
  have hFn : 0 ≤ F.mult w := by
    rw [hF]; exact Int.ediv_nonneg hnn (by exact_mod_cast hmult.pos.le)
  obtain ⟨h, hh⟩ := F.exists_isEqn w
  have hreg := (hh.neg.regularAt_iff).1 (hf w hzx)
  set u : X.functionFieldˣ := Units.mk0 f hf0 with hu
  have hv : ((fnPull s u * h⁻¹ : Y.functionFieldˣ) : Y.functionField) =
      functionFieldMap s f * ((h⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    simp [hu, fnPull]
  have h1 : 0 ≤ E'.ord (fnPull s u * h⁻¹) :=
    (E'.ord_nonneg_iff _).2 (hv ▸ (hE' _).2 hreg)
  rw [E'.ord_mul, E'.ord_inv, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E u, hE'.ord_eq h,
    ← hh.mult_eq] at h1
  have h2 : 0 ≤ E.ord u := by omega
  exact (hE f).1 ((E.ord_nonneg_iff u).1 h2)

end GlobalTheory.Discrepancy
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundaryStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_effective_boundary : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  first | exact @_root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | exact _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | (intros; apply _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealBoundaryMonotone

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem nadel_of_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro k _ _ X _ _ _ p n hp hdim Δ η m G Y _ _ s _ K B hΔ hLM hR N M T hN hMlb r hT hr hcls hMnef
    a Fd A hA hFd J hJ i hi
  haveI := hR.smooth
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hR.proj (pullCart s G - m • K) m
  have hJ' := (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF J).1 hJ
  obtain ⟨e⟩ := GlobalTheory.T.pushforward_ideal_regularity X Y s hR.bir (-F) J hJ'
    (GlobalTheory.T.multiplier_ideal_effective_boundary k X p n hp hdim Δ η m G Y s K B F hΔ hLM hR hF)
  have hv := (GlobalTheory.T.multiplier_vanishing_nef_twist_ample k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF N M T hN hMlb r hT hr
    hcls hMnef a Fd A hA hFd).1 i hi
  exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ i ((twistFunctor N).mapIso e)).symm.toEquiv hv

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingTheorem

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem GlobalTheory.nadelVanishing : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → (letI := algebraΓOfHom p; IsBig k M) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro hP k _ _ X _ _ _ p n hproj hdim Δ η m G hΔ hlm N M T hN hM r hT hr hcls hMnef hMbig J hJ i hi
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, _, s, _, K, B, hres, -, a, Fd, A, hA, hkod⟩ :=
    GlobalTheory.LogResBig.exists_logRes_smul_eq_ample_add_eff hP k X p n hproj hdim η m G hlm.ne_zero ⊥ hZ M hM hMbig
  haveI : IsLocallyNoetherian Y :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hres.smooth.smooth).2.2
  exact GlobalTheory.nadel_of_logRes k X p n hproj hdim Δ η m G Y s K B hΔ hlm hres N M T hN hM r hT hr hcls hMnef a Fd A hA hkod J hJ i hi
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem nadelVanishingPair_of_principalisation (hP : GlobalTheory.Published.Principalisation) :
    GlobalTheory.Published.NadelVanishingPair := by
  intro X _ _ _ p n hproj hdim N Δ m G r M₀ hN hΔ hm hlc hr hnef hbig hcurve
  letI := algebraΓOfHom p
  obtain ⟨η, hlm⟩ := hlc.exists_isLogMult hm
  obtain ⟨J, hJ, hsupp⟩ :=
    exists_isMultIdeal_support_iff_not_kltAt hP ℂ X p n hproj hdim Δ η m G hlm
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hM : M₀.IsLB := hnef.isLB
  have hG : (toLB G).IsLB := isLB_toLB G
  have hP1 : (lbPow N (m * r)).IsLB := isLB_lbPow hN _
  have hP2 : (lbPow (toLB G) r).IsLB := isLB_lbPow hG _
  have hP3 : (lbPow M₀ m).IsLB := isLB_lbPow hM _
  have hD2 : (dual (lbPow (toLB G) r)).IsLB := isLB_dual hP2
  have hD3 : (dual (lbPow M₀ m)).IsLB := isLB_dual hP3
  have hS : (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))).IsLB := isLB_tens hD2 hD3
  have hTl : (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))).IsLB :=
    isLB_tens hP1 hS
  have hclsS : cls _ hS = cls _ hD2 + cls _ hD3 := cls_tens hD2 hD3 hS
  have hclsT : cls _ hTl = cls _ hP1 + cls _ hS := cls_tens hP1 hS hTl
  have hT : IsNef ℂ (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))) := by
    refine ⟨hTl, fun Z hZ => ?_⟩
    have e1 := hZ.interNumRed_of_cls_eq_add hH hTl hP1 hS hclsT
    have e2 := hZ.interNumRed_of_cls_eq_add hH hS hD2 hD3 hclsS
    have e3 := hZ.interNumRed_dual (L := lbPow (toLB G) r) hH hP2
    have e4 := hZ.interNumRed_dual (L := lbPow M₀ m) hH hP3
    have e5 := hZ.interNumRed_lbPow hH hN (m * r)
    have e6 := hZ.interNumRed_lbPow hH hG r
    have e7 := hZ.interNumRed_lbPow hH hM m
    have hq := hcurve Z hZ
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    have hz : ((m : ℤ) * r) * interNumRed ℂ Z ![N] = r * interNumRed ℂ Z ![toLB G] + m * interNumRed ℂ Z ![M₀] := by
      have : ((m : ℚ) * r) * (interNumRed ℂ Z ![N] : ℚ) = r * (interNumRed ℂ Z ![toLB G] : ℚ) + m * (interNumRed ℂ Z ![M₀] : ℚ) := by
        rw [hq]
        field_simp
      exact_mod_cast this
    rw [e1, e2, e3, e4, e5, e6, e7]
    push_cast
    linarith
  have hcls : cls _ hT.isLB = (m * r) • cls N hN - r • toPic G - m • cls M₀ hM := by
    rw [hclsT, hclsS, cls_dual hP2 hD2, cls_dual hP3 hD3, cls_lbPow hN (m * r) hP1, cls_lbPow hG r hP2,
      cls_lbPow hM m hP3]
    have : cls (toLB G) hG = toPic G := rfl
    rw [this]
    abel
  exact ⟨J, hsupp, fun i hi =>
    GlobalTheory.nadelVanishing hP ℂ X p n hproj hdim Δ η m G hΔ.nonneg hlm N M₀ _ hN hM r hT hr hcls hnef hbig J hJ i hi⟩

end GlobalTheory.Discrepancy
end
end
