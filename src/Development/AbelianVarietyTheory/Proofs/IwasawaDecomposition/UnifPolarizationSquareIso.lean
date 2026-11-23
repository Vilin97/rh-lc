module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIsoStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesEvenCharactersFourthPowersAssociatStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFour

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiDoubleCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

section
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_cub (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b) ξ J =
      Units.map (cst ξ).toMonoidHom w := by
  have hp : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp]
  refine val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t _ fun k => ?_
  show (_ ≫ (psum _ _ _).left) ≫ _ = _
  rw [Category.assoc, Over.w, Over.w]; rfl

theorem val_sym (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (y : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L _ _ D.sym (D.xK y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  rw [val_pull hJ]
  have hx : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
  rw [hx]
  refine val_int ξ hJc D.sym _ fun k => ?_
  obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
    fin_cases k
    · exact ⟨_, rfl⟩
    · exact ⟨𝟙 _, rfl⟩
  rw [hq, Category.assoc, Over.w q, Over.w]; rfl

theorem val_rig (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) :
    ∃ w : Rˣ, val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  unfold DegPre.rigK
  rw [val_pull hJ]
  have : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [this]
  exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

end

theorem alg {G : Type} [CommGroup G] (A0 Ay Am A2 Vr C0 C1 S : G)
    (h1 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C0 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * (Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h2 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 = A2 * Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * Am⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h3 : Am * S = Ay) :
    A2 = C0 * C0 * C1 * Vr * Vr * Vr * S⁻¹ * Ay ^ 4 := by
  have hC0 := mul_left_cancel h1
  have hAm : Am = Ay * S⁻¹ := eq_mul_inv_of_mul_eq h3
  subst hC0 hAm
  have e : A2 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 * (Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * (Ay * S⁻¹)⁻¹ * Ay⁻¹ * Vr⁻¹))⁻¹ := by
    rw [h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem val_cubP {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
      (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := val_cub D ξ hJc a a' b
  exact ⟨w, (val_pull hJ _ _ _).trans hw⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I)
    (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  intro R _ _ _ I D y r s hr hs
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.toPre.P.isLB D.toPre.P.A.hom
  have b1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult 0 0 y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have b2 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult y (-y) y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even y) (𝟙 _))
  have vt : ∀ a b : D.toPre.X, val (D.toPre.tau a b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = val (D.toPre.psi (a + b)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J *
      (val (D.toPre.psi a) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val (D.toPre.psi b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val D.toPre.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ :=
    fun a b => GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b
  obtain ⟨w0, hw0⟩ := val_cubP D.toPre ξ hJ hJc 0 0 y
  obtain ⟨w1, hw1⟩ := val_cubP D.toPre ξ hJ hJc y (-y) y
  obtain ⟨w5, hw5⟩ := val_rig D.toPre ξ hJ hJc
  obtain ⟨w6, hw6⟩ := val_sym D.toPre ξ hJ hJc y
  rw [hw6] at ev
  rw [hw0, vt, vt, hw5] at b1
  rw [hw1, vt, vt, vt, hw5] at b2
  rw [add_zero, zero_add] at b1
  rw [add_neg_cancel, zero_add, neg_add_cancel, ← two_nsmul] at b2
  have key := alg _ _ _ _ _ _ _ _ b1 b2 ev
  obtain ⟨u1, g1⟩ : ∃ u : Rˣ, (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * r) := val_psi D.toPre ξ hJ hJc y r hr
  obtain ⟨u2, g2⟩ : ∃ u : Rˣ, (val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * s) := val_psi D.toPre ξ hJ hJc (2 • y) s hs
  obtain ⟨W, key2⟩ : ∃ W : Rˣ, val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J =
      Units.map (cst ξ).toMonoidHom W * (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J) ^ 4 :=
    ⟨w0 * w0 * w1 * w5 * w5 * w5 * w6⁻¹, by rw [key]; simp only [map_mul, map_inv]⟩
  have e : cst ξ (u2 * s) = cst ξ (W * (u1 * r) ^ 4) := by
    rw [← g2, key2, map_mul, map_pow, ← g1, Units.val_mul, Units.val_pow_eq_pow_val]; rfl
  have e2 := cst_injective ξ e
  refine ⟨u2 * (W * u1 ^ 4)⁻¹, ?_⟩
  have h3 : ((W * u1 ^ 4 : Rˣ) : R) * r ^ 4 = u2 * s := by push_cast; rw [e2]; ring
  rw [Units.val_mul, ← _root_.mul_assoc, _root_.mul_comm s, ← h3, _root_.mul_comm, ← _root_.mul_assoc, Units.inv_mul,
    _root_.one_mul]

end GlobalTheory.PsiDoubleCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFourStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  first | exact @GlobalTheory.PsiDoubleCoord.main | exact GlobalTheory.PsiDoubleCoord.main | (intros; apply GlobalTheory.PsiDoubleCoord.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqUnifCoord

theorem associated_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b : R} {n : ℕ}
    (hn : 0 < n) (h : Associated (a ^ n) (b ^ n)) : Associated a b := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn.ne'] at h
    rw [(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at h
    exact ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))
  obtain ⟨u, hu⟩ := h
  set K := FractionRing R
  have inj := IsFractionRing.injective R K
  have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (inj (h0.trans (map_zero _).symm))
  have hb' : algebraMap R K b ≠ 0 := fun h0 => hb (inj (h0.trans (map_zero _).symm))
  have hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]
  have hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))
  have hcd : c * d = 1 := inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b),
    div_self (mul_ne_zero ha' hb')])
  refine ⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩
  show algebraMap R K (a * c) = algebraMap R K b
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' hL
  have hA := admissibleBase_of_completeNormalLocalCharZero hR
  haveI : CharZero R := hR.2.2.2
  haveI : IsIntegrallyClosed R := hR.2.1
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre
  obtain ⟨Φ, w, wL, hw, hwL, hm, hp⟩ := GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL
  have hc := GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe
  refine ⟨xe, fun y r r' hr hr' => ?_⟩
  obtain ⟨⟨s, hs, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))
  obtain ⟨⟨s', hs', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)
  have a1 : Associated s (r ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)
  have a2 : Associated s' (r' ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'
  have a3 : Associated (s ^ 4) (s' ^ 4) :=
    GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'
  refine associated_of_pow (n := 8) (by norm_num) ?_
  have e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4 := by ring
  have e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4 := by ring
  rw [e1, e2]
  exact ((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))

end GlobalTheory.SqUnifCoord
end
end
end
