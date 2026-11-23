module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessLemmaAtNormalPointLogResolutionStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorCenterProperLift
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficientsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkEquivOfFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyAddOrdGtNegOneLogResolution

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.CoeffPlaces

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem supp_neg_le' (D : CartierDiv Z) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le' (D : CartierDiv Z) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

variable [IsLocallyNoetherian Z]

theorem mult_zero'' (z : Z) : (0 : CartierDiv Z).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv Z) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul''' (E : CartierDiv Z) (r : ℕ) (z : Z) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero => rw [zero_nsmul, mult_zero'']; simp
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub'' (D E : CartierDiv Z) (z : Z) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem ord_nonneg_of_regAt' {f : Z.functionField} {z : Z} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem regAt_functionFieldMap' {X : Scheme.{0}} [IsIntegral X] (q : Z ⟶ X) [IsDominant q] (y : Z)
    {f : X.functionField} (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

end GlobalTheory.Discrepancy.CoeffPlaces


open GlobalTheory.Discrepancy.CoeffPlaces in
theorem GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  intro X _ _ p n hproj _ η m g f Y _ _ s _ K B y σ hη hm hres hfB hfy hσ1 hσm hlt E hE
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hres.bir E
  obtain ⟨y', rfl, hE'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p s hres.bir inferInstance E' E hE'E _ hE
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  set F := pullCart s (CartierDiv.principal f) with hFdef
  set G := pullCart s (CartierDiv.principal g) with hGdef
  have hFsupp : F.supp ≤ B := fun v hv => hfB v ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y s _).1 v hv)
  have e : G - m • F - m • K = (G - m • K) + -(m • F) := by abel
  have hsupp : (G - m • F - m • K).supp ≤ B := by
    rw [e]
    exact (CartierDiv.supp_add_le _ _).trans
      (sup_le hres.supp ((supp_neg_le' _).trans ((supp_nsmul_le' _ _).trans hFsupp)))
  have hFm (w : Y) : F.mult w = Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal f (s w))).mult_eq
  have hEqn : (G - m • F).IsEqn y' (fnPull s g / fnPull s f ^ m) :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal g (s y'))).sub
      ((isEqn_pullCart s (CartierDiv.isEqn_principal f (s y'))).nsmul m)
  have hmul (w : Y) : (G - m • F - m • K).mult w = (G - m • K).mult w - m * F.mult w := by
    rw [mult_sub'', mult_sub'', mult_sub'', mult_nsmul''', mult_nsmul''']; ring
  have hlt' : ∀ w, w ⤳ y' → (G - m • F - m • K).mult w < m := by
    intro w hw
    rw [hmul, hFm]
    by_cases hwσ : w = σ
    · subst hwσ
      rw [hσm, hσ1]
      simp only [mul_one, sub_self]
      exact_mod_cast hm
    · have hsw : s w ⤳ s y' := hw.map s.continuous
      have h0 : 0 ≤ Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        ord_nonneg_of_regAt' (regAt_functionFieldMap' s w (regAt_of_specializes hsw hfy))
          (Units.ne_zero _)
      have h1 := hlt w hwσ hsw
      have h2 : (0 : ℤ) ≤ m * Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        mul_nonneg (Int.natCast_nonneg m) h0
      linarith
  have hcrit := (GlobalTheory.T.klt_of_snc_coefficients ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (G - m • F) m B hm
    hres.div hres.snc hsupp y' _ hEqn E' hE').1 hlt'
  have hd : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g / fnPull s f ^ m) =
      discrep E η m g + E.ord f := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hres.bir E' E hE'E n η hη
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, div_eq_mul_inv (fnPull s g), E'.ord_mul, E'.ord_inv,
      E'.ord_pow, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E g,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E f]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [← hd]
  exact hcrit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyAddOrdGtNegOneLogResolutionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  first | exact @GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes | exact GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes | (intros; apply GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartier

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUp

theorem regAt_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    (z : Y) {f : X.functionField} (h : RegAt (s z) f) : RegAt z (functionFieldMap s f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨s.stalkMap z a, (functionFieldMap_algebraMap s z a).symm⟩

theorem scheme_ord_zero {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Scheme.ord (0 : Y.functionField) z = 0 := by
  exact congrFun Scheme.ord_zero z

theorem place_ord_eq {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} {E : DivOver q} {z : Y} (h : E.IsAt z) (f : Y.functionField) :
    (placeEquiv q E).ord f = Scheme.ord f z := by
  by_cases hf : f = 0
  · subst hf
    rw [scheme_ord_zero]
    simp [Place.ord]
  · exact h.ord_eq (Units.mk0 f hf)

theorem ring_eq_of_isAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    {E F : DivOver q} {z : Y} (hE : E.IsAt z) (hF : F.IsAt z) :
    (placeEquiv q E).ring = (placeEquiv q F).ring :=
  SetLike.ext fun f => (hE f).trans (hF f).symm

def stalkEquiv {Y : Scheme.{0}} [IsIntegral Y] (w : Y) : Y.presheaf.stalk w ≃+* locRing w :=
  RingEquiv.ofBijective (algebraMap (Y.presheaf.stalk w) Y.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem stalkEquiv_apply {Y : Scheme.{0}} [IsIntegral Y] (w : Y) (a : Y.presheaf.stalk w) :
    ((stalkEquiv w a : locRing w) : Y.functionField) = algebraMap _ Y.functionField a := rfl

theorem map_maximalIdeal_equiv {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (φ : R ≃+* R') :
    (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R' := by
  ext a
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩ h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb
    exact hb ((isUnit_map_iff φ b).1 h)
  · intro ha
    refine ⟨φ.symm a, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    exact ha (by simpa using h.map φ)

end GlobalTheory.FieldPair.AdjUp


open GlobalTheory.FieldPair.AdjUp in
theorem GlobalTheory.FieldPair.mult_lt_of_adjKlt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  intro X _ _ p n _ _ x m g Y _ _ s _ K B y σ S S' hx hm hres hover hσ hmσ hadj v w hvσ hvw hσw hwy
  by_cases hv0 : (pullCart s (CartierDiv.principal g) - m • K).mult v ≤ 0
  · exact lt_of_le_of_lt hv0 (by exact_mod_cast hm)
  have hv0' : (pullCart s (CartierDiv.principal g) - m • K).mult v ≠ 0 := by omega
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := Discrepancy.CanonIso.isNormalScheme_of_smooth' (s ≫ p)
  have hmσ0 : (pullCart s (CartierDiv.principal g) - m • K).mult σ ≠ 0 := by
    rw [hmσ]; exact_mod_cast hm.ne'
  have hvB : v ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hv0')
  have hσB : σ ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hmσ0)
  have hv1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hv0'
  have hσ1 := hσ.coheight_eq_one
  obtain ⟨w', t, u, hw'w, hvw', hσw', hdim, hspan, htσ, huv, hB⟩ :=
    GlobalTheory.SncMeet.exists_meet_point Y (s ≫ p) n B hres.snc v σ w hvB hσB hv1 hσ1 hvσ hvw hσw
  obtain ⟨Ev, hEv⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv1
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hres.bir
  have hc : ∀ a, e (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a := fun a =>
    RingHom.congr_fun (EtaleKlt.functionFieldMap_comp_constFn p s) a
  have hadj' := GlobalTheory.FieldPair.adjKlt_ringEquiv (Cartier.constFn p) (Cartier.constFn (s ≫ p)) e hc n x (locRing y)
    (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) (placeEquiv p S) (placeEquiv (s ≫ p) S') hx
    (fun a => (hover a).symm) hadj
  rw [Finsupp.mapDomain_single] at hadj'
  have hη : dForm (Cartier.constFn (s ≫ p)) (e ∘ x) =
      EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) := by
    rw [EtaleKlt.ratPull, formMap_dForm]
    rfl
  have hη0 : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hadj.form_ne_zero ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hres.bir n).1
      (h0.trans (map_zero _).symm))
  rw [hη] at hadj'
  unfold AdjKlt at hadj'
  have hdisc : ∀ (P : DivOver (s ≫ p)) (z : Y), P.IsAt z →
      (placeEquiv (s ≫ p) P).disc (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x))
        (Finsupp.single (e g) (1 / (m : ℚ))) =
        -((pullCart s (CartierDiv.principal g) - m • K).mult z : ℚ) / m := by
    intro P z hP
    have h1 := disc_placeEquiv P (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g)
    exact h1.trans (discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη0 K _ m hm hres.div P z (fnPull s g) hP
      (isEqn_pullCart s (CartierDiv.isEqn_principal g (s z))))
  have hTQ : (locRing y).map e.toRingHom ≤ locRing w' := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : s w' ⤳ y := (hw'w.map s.continuous).trans hwy
    exact regAt_map s w' (regAt_of_specializes h1 ha)
  have hQ := isLocModel_locRing (p := s ≫ p) w'
  have key := hadj'.2.2 (locRing w') hQ (stalkEquiv w' t) (stalkEquiv w' u) (placeEquiv (s ≫ p) Ev) hTQ
    ?_ ?_ ((isPrimeOf_placeEquiv S' w').2 ⟨σ, hσw', hσ⟩) ((isPrimeOf_placeEquiv Ev w').2 ⟨v, hvw', hEv⟩)
    (by rw [stalkEquiv_apply, place_ord_eq hσ]; exact htσ)
    (by rw [stalkEquiv_apply, place_ord_eq hEv]; exact huv) ?_
  · rw [hdisc Ev v hEv] at key
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    rw [lt_div_iff₀ hm'] at key
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult v : ℚ) < m := by linarith
    exact_mod_cast this
  · have h1 : Ideal.span {stalkEquiv w' t, stalkEquiv w' u} = (Ideal.span {t, u}).map (stalkEquiv w') := by
      rw [Ideal.map_span]; simp [Set.image_insert_eq]
    rw [h1, hspan]
    haveI := hQ.isLocalRing
    exact map_maximalIdeal_equiv _
  · exact (ringKrullDim_eq_of_ringEquiv (stalkEquiv w')).symm.trans hdim
  · intro P hP h1 h2
    obtain ⟨P₀, rfl⟩ := (placeEquiv (s ≫ p)).surjective P
    obtain ⟨z, hzw', hz⟩ := (isPrimeOf_placeEquiv P₀ w').1 hP
    rw [hdisc P₀ z hz]
    have hz1 := hz.coheight_eq_one
    have hzσ : z ≠ σ := by rintro rfl; exact h1 (ring_eq_of_isAt hz hσ)
    have hzv : z ≠ v := by rintro rfl; exact h2 (ring_eq_of_isAt hz hEv)
    have hzB : z ∉ B := fun hzB => (hB z hzB hz1 hzw').elim hzv hzσ
    have h0 : (pullCart s (CartierDiv.principal g) - m • K).mult z = 0 := by
      by_contra h0
      exact hzB (hres.supp (CartierDiv.mem_supp_of_mult_ne_zero h0))
    rw [h0]
    simp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartierStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.log_residue_dominant_cartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  first | exact @GlobalTheory.FieldPair.mult_lt_of_adjKlt | exact GlobalTheory.FieldPair.mult_lt_of_adjKlt | (intros; apply GlobalTheory.FieldPair.mult_lt_of_adjKlt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InversionOfAdjunctionProj

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory

theorem inversion_of_adjunction_proj : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  intro hP X _ _ p n hproj hdim x m g f y S hx hm hnorm hreg hS hSf hdisc hE hadj E hEy
  have hη : (dForm (Cartier.constFn p) x : RatForms p n) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_dForm_of_trBasis _ hx).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨Y, hYi, hYn, s, hsd, K, B, hres, hB, hconn⟩ :=
    GlobalTheory.T.connectedness_lemma_at_normal_point_logResolution hP X p n hproj hdim (dForm (Cartier.constFn p) x) m (CartierDiv.principal g)
      (CartierDiv.principal f).supp hη hm (CartierDiv.supp_ne_top _)
  haveI := hYi; haveI := hYn; haveI := hsd
  obtain ⟨z, hzy, hSz⟩ := (isPrimeOf_placeEquiv S y).1 hS
  have hbir := hres.bir
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  obtain ⟨S', hS'⟩ := DivOver.exists_over ℂ X Y p s hbir S
  obtain ⟨σ, hσz, hS'σ⟩ := DivOver.isAt_lift ℂ X Y p s hbir inferInstance S' S hS' z hSz
  haveI := hres.smooth
  have hη' : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1
      (h0.trans (map_zero _).symm))
  have hd := discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη' K (pullCart s (CartierDiv.principal g)) m
    hm hres.div S' σ (fnPull s g) hS'σ
    (isEqn_pullCart s (hσz ▸ CartierDiv.isEqn_principal g z))
  have hdd : discrep S' (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g) =
      discrep S (dForm (Cartier.constFn p) x) m g := by
    simp only [discrep]
    rw [BirOrd.formOrd_ratPull_of_over ℂ X Y p s hbir S' S hS' n _ hη,
      DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' g]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmult : (pullCart s (CartierDiv.principal g) - m • K).mult σ = m := by
    rw [hdd, hdisc] at hd
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult σ : ℚ) = m := by
      field_simp at hd
      linarith
    exact_mod_cast this
  have hsσ : s σ ⤳ y := hσz ▸ hzy
  have heff : ∀ z', z' ⤳ y → ∀ E' : DivOver p, E'.IsAt z' → ∀ g',
      (CartierDiv.principal g).IsEqn z' g' →
      discrep E' (dForm (Cartier.constFn p) x) m g' ≤ 0 := by
    intro z' hz' E' hE' g' hg'
    have h1 := hE E' ((isPrimeOf_placeEquiv E' y).2 ⟨z', hz', hE'⟩)
    have h2 : E'.ord g' = E'.ord g := by
      rw [hE'.ord_eq, hE'.ord_eq, ← hg'.mult_eq, (CartierDiv.isEqn_principal g z').mult_eq]
    simp only [discrep] at h1 ⊢
    rw [h2]
    exact h1
  have hnb := GlobalTheory.T.log_residue_dominant_cartier X p n hproj hdim x m g Y s K B y σ S S' hx hm hres hS' hS'σ hmult hadj
  have hlt := hconn y σ hnorm heff hmult hsσ hnb
  have hordσ : Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 := by
    rw [← hS'σ.ord_eq, DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' f, hSf]
  exact GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution X p n hproj hdim _ m g f Y s K B y σ hη hm hres hB hreg hordσ hmult hlt E hEy

end GlobalTheory
end
end
