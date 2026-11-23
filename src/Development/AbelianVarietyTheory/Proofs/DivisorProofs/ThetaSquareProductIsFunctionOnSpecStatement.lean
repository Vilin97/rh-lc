module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint

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

namespace GlobalTheory.IntPointFn

theorem comp_padd_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0)).left = b.left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero]
  simp only [padd, comp_one]
  show (b ≫ (𝟙 D.P.A * 1)).left = b.left
  rw [_root_.mul_one, Category.comp_id]

theorem comp_toUnit_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ D.c 0).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq, ← Category.assoc,
    toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem comp_toUnit_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, ← Category.assoc, toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

end GlobalTheory.IntPointFn

namespace GlobalTheory.IntPointFn

theorem fn_of_theta : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  intro V _ _ D θ b t ht ρ₀ hρ
  have hL := D.P.isLB
  have hu := mulGen_isGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀) ht (invGen_isGen _ _ _ _ hρ)
  have hF : FormEq (Sum.elim (fun k => b.left ≫ D.famφB 0 k)
      (Sum.elim ![(η[D.P.A]).left, b.left] (fun _ : PUnit => eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (DegPre.lineε 1) (fun _ : PUnit => -(1 : ℤ))))
      (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → ℤ) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
      Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
      comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    abel
  obtain ⟨s', hs'⟩ := exists_sec hL hF (pullMulSec (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) b.left
    (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀)) hu)
  have hle : (⊤ : (Sp V).Opens) ≤ LB.wchart D.P.L (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → D.P.L.ι) :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))), fun Z r z J hJ => ?_⟩
  have e1 := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ hu r z hJ)
  rw [val_mul hJ, val_inv,
    sval_of s' r z J (PEmpty.elim : PEmpty → D.P.L.ι) (fun k => k.elim)] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)))) =
      ((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)) := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have e3 := gs_res r z hle (by trivial) (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))
  rw [e2]
  erw [e3, e1]
  rw [Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel,
    Units.val_one, _root_.mul_one]

end GlobalTheory.IntPointFn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpec

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

namespace GlobalTheory.IntPointFnSq

theorem c_comp_inv (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c χ).left ≫ (ι[D.P.A]).left = (D.c (-χ)).left := by
  rw [← Over.comp_left]
  congr 1
  have h : D.c χ * D.c (-χ) = 1 := by
    rw [← GlobalTheory.Poinc.ThetaOne.c_zero D, ← add_neg_cancel χ, D.c_add]; rfl
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem c_eq_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c (χ + -χ)).left = (η[D.P.A]).left := by
  rw [add_neg_cancel, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]


open GlobalTheory.IntPointFn in
theorem fn_of_theta_sq : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro V _ _ D θ b χ t ht χt hχt τ hτ
  have hL := D.P.isLB
  have e0 : (D.c 0).left = (η[D.P.A]).left := by rw [GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]
  have e1 := c_comp_inv V D χ
  have e2 := c_eq_eta V D χ
  have e4 : (b * D.c χ).left = (D.c χ * b).left := by rw [_root_.mul_comm]
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t t) (LB.mulGen D.P.L _ _ _ _ χt χt))
    (LB.pullGen D.P.L _ _ D.sym (D.c χ).left)) (LB.invGen D.P.L _ _ τ))
    (LB.invGen D.P.L _ _ (LB.mulGen D.P.L (Y := Sp V) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig))
  have hu : u.IsGen := by
    refine mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht ht) (mulGen_isGen _ _ _ _ _ _ _ hχt hχt))
      (pullGen_isGen _ _ _ _ D.sym_gen _)) (invGen_isGen _ _ _ _ hτ))
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ D.rig_gen D.rig_gen))
  obtain ⟨s', hs'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_powSec hL (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b * D.c χ).left 2 u hu (K' := PEmpty) PEmpty.elim PEmpty.elim (fun U _ f => by
      simp only [u, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
        Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, DegPre.gtε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
        comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec, e0, e1, e2, e4]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      abel)
  obtain ⟨a, ha⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_fn s'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a, fun Z r z J hJ => ?_⟩
  have e2' : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a) = a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e2', ← ha, hs' Z r z J hJ]
  congr 1
  simp only [u, val_mul hJ, val_inv, val_pull hJ, rigV]
  simp only [pow_two]

end GlobalTheory.IntPointFnSq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpecStatement

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

theorem _root_.GlobalTheory.T.thetaSquare_product_isFunction_on_spec : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  first | exact @GlobalTheory.IntPointFnSq.fn_of_theta_sq | exact GlobalTheory.IntPointFnSq.fn_of_theta_sq | (intros; apply GlobalTheory.IntPointFnSq.fn_of_theta_sq <;> assumption)
end
end
