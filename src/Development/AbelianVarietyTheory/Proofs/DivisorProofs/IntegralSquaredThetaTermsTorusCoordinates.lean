module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalProductIdentityOfGenericPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitCoefficientOfThetaSquareIntegralTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSqGenericPointEqMonomialMulSymmetricStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyCoefficientIntegralTorusPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpecStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem kap_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  intro V _ _ D N b hbN t ht κ hκn hgen Z r z J hJ
  have G := ((SymFrame.grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (SymFrame.grep_kap κ hκn.1 b)
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      rw [Fin.prod_univ_two, hbN, ← SymFrame.eta_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, DegPre.lineε, Category.comp_id,
        Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      rw [← natCast_zsmul]
      push_cast
      module) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := a.trans (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs (Over.mk r) (toUnit _) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact a.symm

end GlobalTheory.Poinc.Sep.FrameInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.integralFrame_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | exact GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationKEqOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.PsiZero

theorem psi_zero_mul_rigK : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  intro V _ _ D hB Z r z J hJ

  let T : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (TK V).hom)
  let ρ : T ⟶ TK V := Over.homMk r rfl
  have hcub : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) r z J = 1 := by
    have e := val_cub D.cub ρ hJ (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0)
    refine e.trans ?_
    rw [GlobalTheory.Poinc.ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face 1 1
  have hc := (val_mul hJ _ _ r).symm.trans ((val_corr hJ (hB 0 0 0) r).trans (val_mul hJ _ _ r))
  rw [hcub, _root_.mul_one,
    congrArg (fun w => val (D.tau w 0) r z J) (add_zero (0 : D.X))] at hc
  have ht : val (D.tau 0 0) r z J = 1 := (mul_eq_left.1 hc.symm)
  unfold DegPre.tau at ht
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) r z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul] at ht
  rw [← mul_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.Poinc.Sep.PsiZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiZeroMulRigidificationKEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.psi_zero_mul_rigidificationK_eq_one : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK | exact GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK | (intros; apply GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSquaredThetaTermsTorusCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

theorem gs_top {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem unit_map_map {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.CoefInt

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem integral_sq_terms : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult →
    ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
    (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X)
      (hs : ∀ k, IsUnit (s (.inr k))),
    GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) →
    (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) →
    ∃ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
      (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)))
      (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε))
      (s₀ : V₁) (G : X → C → V₁),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) ∧
      IsUnit s₀ ∧
      (∀ mu c, u mu c ^ 2 * s₀ = ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) * G mu c) ∧
      ∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro N₁ hN₁ V₁ _ _ _ hV hunit D hPE hTB X C _ e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ N₁ := by omega
  obtain ⟨th, g, b, w, hgb, ho, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ := thetaTerms_integral D hN1 e _ hT
  obtain ⟨θ, hθ, -, hlamE, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlamE (FractionRing V₁) th
  have hψ0 := GlobalTheory.T.psi_zero_mul_rigidificationK_eq_one V₁ D hTB

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D) ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)
    obtain ⟨ε', hε'⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε' z J hJ, gm_top_eq, unit_map_map]
  choose t htg htv using ht

  have hχ : ∀ mu c, ∃ χt : LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε), χt.IsGen ∧
      (∀ z J, Good D.P.L z J → val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J =
        val ((g c).s (e mu)) (𝟙 _) z J) ∧
      (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ D.c (e mu))
        (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c ^ i) (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c) =
        val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J ^ N₁) := by
    intro mu c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D)
      ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε
    obtain ⟨ε', h1, h2⟩ := char_unit hN1 (g c) (b c) (hgb c) (ho c) (e mu) t' ht'
    obtain ⟨χt, hg, hv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨χt, hg, fun z J hJ => Units.ext ?_, fun z J hJ => Units.ext ?_⟩
    · rw [hv _ _ z J hJ, Units.val_mul, h1 z J hJ, gm_top_eq, unit_map_map]
    · rw [h2 z J hJ, hv _ _ z J hJ, mul_pow, Units.val_mul]
      simp only [Units.val_pow_eq_pow_val]
      rw [gm_top_eq, unit_map_map]
  choose χt hχg hχv hχc using hχ

  have hG : ∀ mu c, ∃ G : V₁, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
          (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
            (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := fun mu c =>
    GlobalTheory.T.thetaSquare_product_isFunction_on_spec V₁ D θ (b c) (e mu) (t c) (htg c) (χt mu c) (hχg mu c) (τ₀ (e mu) (-e mu)) (hτ _ _).1
  choose G hGv using hG
  have hk := fun mu => GlobalTheory.T.psi_sq_genericPoint_eq_monomial_mul_symmetric V₁ D hPE hψ0 τ₀ _ _ _ hτ (e mu)
  choose k hkv hkψ using hk
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have key : ∀ mu c, algebraMap V₁ (FractionRing V₁) (u mu c * mo mu) ^ 2 =
      lam ^ 2 * (k mu : FractionRing V₁) * algebraMap V₁ (FractionRing V₁) (G mu c) := by
    intro mu c
    have E1 := GlobalTheory.T.thetaFamily_coefficient_integral_torusPoint V₁ D θ lam th hlam hψ0 (e mu) (g c) (b c) (hgb c) (w c) _ (hcoef mu c) z J hJ
    have E2 := hkψ mu z J hJ
    have E3 := hGv mu c _ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J hJ
    rw [gs_top, htv c z J hJ, hχv mu c z J hJ] at E3
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at E2 E3
    apply cst_inj z
    rw [cst_eq] at E2 E3
    rw [cst_eq, cst_eq] at E1
    rw [cst_eq, cst_eq, map_pow (cstH z), E1, map_mul (cstH z), map_mul (cstH z), map_pow (cstH z), E3,
      mul_pow, mul_pow, mul_pow, mul_pow, E2]
    ring

  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hsplit : ∀ mu, (k mu : FractionRing V₁) =
      (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inl j)) ^ ε (.inl j) (e mu) (e mu)) *
      ∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu) := by
    intro mu
    rw [hkv mu, ← Fintype.prod_sum_type (fun j => algebraMap V₁ (FractionRing V₁) (s j) ^ ε j (e mu) (e mu))]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hk0 : (k 0 : FractionRing V₁) = 1 := by
    rw [hkv]; simp
  have hl0 : lam ^ 2 * algebraMap V₁ (FractionRing V₁) (G 0 c₀) = 1 := by
    have := key 0 c₀
    rw [hc₀, map_one, one_pow, hk0, _root_.mul_one] at this
    exact this.symm
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.isUnit_coefficient_of_thetaSquare_integralTorsion N₁ hN₁ V₁ hV hunit D θ hθ C b hcov
  have hb1 : b c₁ * D.c (e 0) = b c₁ := by rw [map_zero, ThetaOne.c_zero, _root_.mul_one]
  have hG1 : IsUnit (G 0 c₁) := hc₁ (G 0 c₁) (fun Z r z J => val (t c₁) r z J ^ 2 * val (χt 0 c₁) r z J ^ 2 *
      val D.sym (r ≫ (D.c (e 0)).left) z J * (val (τ₀ (e 0) (-e 0)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹)
    (fun Z r z J hJ => by rw [hGv 0 c₁ Z r z J hJ, hb1])
  have hs₀u : IsUnit (G 0 c₀) := by
    have k1 := key 0 c₁
    rw [hk0, _root_.mul_one] at k1
    refine IsUnit.of_mul_eq_one ((u 0 c₁ * mo 0) ^ 2 * ↑hG1.unit⁻¹) (hinj ?_)
    rw [map_mul, map_mul, map_one, map_pow, k1]
    have hGne : algebraMap V₁ (FractionRing V₁) (G 0 c₁) * algebraMap V₁ (FractionRing V₁) ↑hG1.unit⁻¹ = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    linear_combination (algebraMap V₁ (FractionRing V₁) (G 0 c₀) * lam ^ 2) * hGne + hl0
  have hP : ∀ mu, algebraMap V₁ (FractionRing V₁) ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
    intro mu
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    change (((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom ((hs k).unit ^ ε (.inr k) (e mu) (e mu)) :
      (FractionRing V₁)ˣ)) : FractionRing V₁) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec]
    rfl
  refine ⟨θ, b, t, χt, G 0 c₀, G, hθ, hbN, fun c => ⟨htg c, fun κ hκ Z r z' J' hJ' => ?_⟩,
    fun mu c => ⟨hχg mu c, fun T z' J' hJ' =>
      GlobalTheory.T.cubicalProduct_identity_of_genericPoint V₁ D N₁ (b c) (D.c (e mu)) (hbN c) (χt mu c) (hχg mu c) (hχc mu c) T z' J' hJ'⟩,
    hs₀u, fun mu c => ?_, hGv⟩
  · refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D N₁ (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · apply hinj
    have km := key mu c
    rw [hsplit, map_mul, mul_pow, ← hmo2 mu] at km
    have hmo0 : algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ hinj).2 (hmo mu).1)
    have h3 : algebraMap V₁ (FractionRing V₁) (u mu c) ^ 2 =
        lam ^ 2 * (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
          algebraMap V₁ (FractionRing V₁) (G mu c) :=
      mul_left_cancel₀ hmo0 (by linear_combination km)
    rw [map_mul, map_mul, map_pow, hP, h3]
    linear_combination ((∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
      algebraMap V₁ (FractionRing V₁) (G mu c)) * hl0

end GlobalTheory.Poinc.Sep.CoefInt
end
end
end
