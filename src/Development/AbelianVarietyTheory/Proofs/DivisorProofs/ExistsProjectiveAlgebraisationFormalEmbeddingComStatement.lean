module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormLimitIdeal
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReduction

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.PolyLoc

open MvPolynomial

theorem exists_homogeneous_coeff_mem {σ R : Type} [CommRing R] (J : Ideal R) (i : σ) (g : MvPolynomial σ R)
    (hg : ∀ m, AddMonoidAlgebra.coeff g m ∈ J) : ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - g := by
  let Q : MvPolynomial σ R → Prop := fun p => ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - p
  have h0 : Q 0 := ⟨0, fun d _ => ⟨0, isHomogeneous_zero _ _ _, fun m => by exact J.zero_mem,
    by rw [sub_zero]; exact dvd_zero _⟩⟩
  have hadd : ∀ p q, Q p → Q q → Q (p + q) := by
    rintro p q ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨max e e', fun d hd => ?_⟩
    obtain ⟨G, hG, hGJ, hGd⟩ := he d (le_of_max_le_left hd)
    obtain ⟨G', hG', hGJ', hGd'⟩ := he' d (le_of_max_le_right hd)
    refine ⟨G + G', hG.add hG', fun m => by rw [MvPolynomial.coeff_add]; exact J.add_mem (hGJ m) (hGJ' m), ?_⟩
    rw [add_sub_add_comm]
    exact hGd.add hGd'
  have hmon : ∀ v (c : R), c ∈ J → Q (monomial v c) := by
    intro v c hc
    refine ⟨v.degree, fun d hd => ⟨monomial v c * X i ^ (d - v.degree), ?_, fun m => ?_, ?_⟩⟩
    · have := (isHomogeneous_monomial (R := R) c (rfl : v.degree = v.degree)).mul (isHomogeneous_X_pow i (d - v.degree))
      rwa [Nat.add_sub_cancel' hd] at this
    · classical
      rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, _root_.mul_one]
      split_ifs
      · exact hc
      · exact J.zero_mem
    · rw [← mul_sub_one]
      exact (sub_one_dvd_pow_sub_one _ _).mul_left _
  rw [g.as_sum]
  exact Finset.sum_induction _ Q hadd h0 fun v _ => hmon v _ (hg v)

theorem exists_X_pow_mul_mem_vanIdeal {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hc : ⨆ j, nonzeroLocus (s j) = ⊤)
    (ha : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (r : ∀ j, Fin (m + 1) → Γ(X, nonzeroLocus (s j)))
    (hr : ∀ j, IsRatioFamily s j (r j)) (i : Fin (m + 1)) {Q : MvPolynomial (Fin (m + 1)) R} {e : ℕ}
    (hQ : Q.IsHomogeneous e) (h0 : eval₂Hom (cst f _) (r i) Q = 0) :
    ∃ c : ℕ, MvPolynomial.X i ^ c * Q ∈ vanIdeal f s := by
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) Q = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr j).gs_form f hj hk hQ).symm.trans ((hr i).gs_form f hi hk hQ)
    rw [h0, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, (mem_vanIdeal _ _ _).2 ?_⟩
  refine (mem_vanishingForms_of_ratios f hc r hr ((isHomogeneous_X_pow i _).mul hQ) fun j => ?_).2
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' hle
  rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]

theorem app_eval_eq_zero {R : Type} [CommRing R] {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (β : X' ⟶ X) {H : LB X} {H' : LB X'} {w : LB.Iso H' (H.pull β)} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    {s' : Fin (m + 1) → LB.Sec H'} (hH : H.IsLB) (hH' : H'.IsLB) (hrel : ∀ j, Rel β w (s j) (s' j))
    (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr : IsRatioFamily s i r)
    {F : MvPolynomial (Fin (m + 1)) R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal (β ≫ f) s') :
    (β.app (nonzeroLocus (s i))).hom (eval₂Hom (cst f _) r F) = 0 := by
  refine fn_ext fun z hz => ?_
  rw [gs_pull (𝟙 X') β z _ hz, Category.id_comp, LBGerm.gs_zero _ z _ hz]
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have e₁ := Rel.form hrel f hF z k k' hk hk'
  rw [(mem_vanIdeal _ _ _).1 h0 k', LBGerm.gs_zero _ z _ hk', mul_zero] at e₁
  have e₂ := congrArg (β.stalkMap z).hom (hr.gs_form f hz hk hF)
  rw [map_mul, map_pow, gs_stalkMap_comp β (𝟙 X) z _ hk, gs_stalkMap_comp β (𝟙 X) z _ hk,
    gs_stalkMap_comp β (𝟙 X) z _ hz] at e₂
  simp only [Category.comp_id] at e₂
  rw [e₁] at e₂
  have u := (mem_nonzeroLocus_iff_pull (s i) β z hk).1 hz
  exact ((u.pow t).mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.FormalAlg.PolyLoc


open GlobalTheory.FormalAlg.PolyLoc MvPolynomial in
theorem GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  open MvPolynomial GlobalTheory.FormalAlg.PolyLoc in
    intro R _ J X X' f β q hpb H H' w n s s' hH hH' _ hrel hva t F hF h0 i
    obtain ⟨hc, hva⟩ := hva
    choose ha r hr hsur using hva
    have hR : ∀ j, IsRatioFamily s j (r j) := hr
    set φ := MvPolynomial.eval₂Hom (AbLaw.cst f (nonzeroLocus (s i))) (r i) with hφ
    have hker := ((GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J X X' f β q hpb).2.2 _ (ha i)).2
    have hβ : (β.app (nonzeroLocus (s i))).hom (φ F) = 0 := app_eval_eq_zero f β hH hH' hrel i (r i) (hR i) hF h0
    have hJ : φ F ∈ (Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J).map φ := by
      have h2 : φ F ∈ J.map (AbLaw.cst f (nonzeroLocus (s i))) := hker ▸ (RingHom.mem_ker.2 hβ)
      have h3 : AbLaw.cst f (nonzeroLocus (s i)) = φ.comp C := by
        ext a
        simp [hφ]
      rwa [h3, ← Ideal.map_map] at h2
    obtain ⟨g, hg, hgF⟩ := (Ideal.mem_map_iff_of_surjective φ (hsur i)).1 hJ
    rw [MvPolynomial.mem_map_C_iff] at hg
    obtain ⟨e, he⟩ := exists_homogeneous_coeff_mem J i g hg
    obtain ⟨G₁, hG₁, hG₁J, hdvd⟩ := he (t + e) (Nat.le_add_left e t)
    have hQ : (MvPolynomial.X i ^ e * F - G₁).IsHomogeneous (t + e) := by
      have := (isHomogeneous_X_pow i e).mul hF
      rw [Nat.add_comm e t] at this
      exact this.sub hG₁
    have hφQ : φ (MvPolynomial.X i ^ e * F - G₁) = 0 := by
      obtain ⟨P, hP⟩ := hdvd
      have hx : φ (MvPolynomial.X i) = 1 := by rw [hφ, eval₂Hom_X']; exact (hR i).self_eq_one
      have hG : G₁ = g + (MvPolynomial.X i - 1) * P := by rw [← hP]; ring
      rw [hG, map_sub, map_mul, map_pow, hx, one_pow, _root_.one_mul, map_add (f := _), map_mul, map_sub, hx, map_one, sub_self,
        zero_mul, add_zero, hgF, sub_self]
    obtain ⟨c, hc'⟩ := exists_X_pow_mul_mem_vanIdeal f hc ha r hR i hQ hφQ
    refine ⟨c + e, MvPolynomial.X i ^ c * G₁, ?_, fun m => ?_, ?_⟩
    · have := (isHomogeneous_X_pow i c).mul hG₁
      convert this using 1
      ring
    · have h4 : MvPolynomial.X i ^ c * G₁ ∈ Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J :=
        Ideal.mul_mem_left _ _ (mem_map_C_iff.2 hG₁J)
      exact mem_map_C_iff.1 h4 m
    · convert hc' using 1
      ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReductionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  first | exact @GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | exact GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | (intros; apply GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousCorrectionNextThickening

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem veryAmpleBy_comp_quotient {X : Scheme.{0}} {R : Type} [CommRing R] (J : Ideal R)
    (f : X ⟶ Spec (CommRingCat.of (R ⧸ J))) (H : LB X) {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (h : VeryAmpleBy f H s) :
    VeryAmpleBy (f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) H s := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨ha, r, hr, hsurj⟩ := h2 i
  refine ⟨ha, r, hr, fun y => ?_⟩
  obtain ⟨P, rfl⟩ := hsurj y
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P
  refine ⟨P', ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, cst_comp_spec]

theorem exists_homogeneous_correction_succ : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ F - G ∈ vanIdeal ((Y (e + 1)).hom ≫ thick R I (e + 1)) (s (e + 1)) := by
  intro R _ _ I Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have hVAR : ∀ e, VeryAmpleBy ((Y e).hom ≫ thick R I e) (H e) (s e) := fun e =>
    veryAmpleBy_comp_quotient _ _ _ _ (hVA e)
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hpb := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  exact GlobalTheory.T.homogeneous_correction_next_level_alt R I n (fun e => vanIdeal ((Y e).hom ≫ thick R I e) (s e))
    (fun e _ _ _ h => mem_vanIdeal_of_sat _ _ (hVA e).1 h)
    (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
      rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
    (fun e t F hF hK i => GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left
      ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom (hpb e) (H (e + 1)) (H e) (v e) n (s (e + 1)) (s e)
      (hH _).1 (hH _).1 (hH e).2 (hs e) (hVAR (e + 1)) t F hF (by rw [c₁]; exact hK) i)

end GlobalTheory.FormalAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousCorrectionNextThickeningStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_homogeneous_correction_next_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ F - G ∈ vanIdeal ((Y (e + 1)).hom ≫ thick R I (e + 1)) (s (e + 1)) := by
  first | exact @GlobalTheory.FormalAlg.exists_homogeneous_correction_succ | exact GlobalTheory.FormalAlg.exists_homogeneous_correction_succ | (intros; apply GlobalTheory.FormalAlg.exists_homogeneous_correction_succ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingCom

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

theorem GlobalTheory.FormalAlg.exists_projective_of_formal_embedding : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j)) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e)) → F ∈ vanIdeal B.hom s' := by
  intro V _ _ I hc Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V I (e + 1) = (Y e).hom ≫ thick V I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e => vanIdeal ((Y e).hom ≫ thick V I e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V I e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneous_correction_next_thickening V I Y β hβ H v hH n s hs hva
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => (mem_vanIdeal _ _ _).2 (hB' t F hF h)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, hF₁, hK, hG⟩ := GlobalTheory.Degen.exists_form_limit_ideal V I hc _ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
      (fun e F hF h => ht₀ t ht e F hF h) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub]
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hG d)
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j)) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e)) → F ∈ vanIdeal B.hom s' := by
  first | exact @GlobalTheory.FormalAlg.exists_projective_of_formal_embedding | exact GlobalTheory.FormalAlg.exists_projective_of_formal_embedding | (intros; apply GlobalTheory.FormalAlg.exists_projective_of_formal_embedding <;> assumption)
end
end
