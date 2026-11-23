module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjectionsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActsOnTorsionLabelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

-- Source module: Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerExamples

variable {S : Scheme.{0}}

theorem hom_ext {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {T : Over S}
    {x y : T ⟶ G'} (h : ∀ i, x ≫ p.pr i = y ≫ p.pr i) : x = y :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem comm_of_pow {G' G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsCommMonObj G' where
  mul_comm := hom_ext p fun i => by
    have := p.hom i
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

theorem pow_unique {G₁ G₂ G : Over S} [GrpObj G₁] [GrpObj G₂] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G₁ G j) (q : IsPowGrp G₂ G j) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ ∀ i, e.hom ≫ q.pr i = p.pr i := by
  have he : ∀ i, (p.lim.conePointUniqueUpToIso q.lim).hom ≫ q.pr i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp q.lim ⟨i⟩
  refine ⟨p.lim.conePointUniqueUpToIso q.lim, ⟨hom_ext q fun i => ?_, hom_ext q fun i => ?_⟩, he⟩
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom (q.pr i),
      ← Category.assoc, tensorHom_comp_tensorHom, he i]

end GlobalTheory.PowerExamples
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroups

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

def matAddEquiv {M : Type*} [AddCommGroup M] (S : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) :
    (Fin 8 → M) ≃+ (Fin 8 → M) where
  toFun w v := ∑ u, S v u • w u
  invFun w v := ∑ u, S.adjugate v u • w u
  left_inv w := by
    funext v
    have h : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv w := by
    funext v
    have h : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

def sumChars {X X' : Type*} [AddCommGroup X] [AddCommGroup X'] (c : Fin 8 → (X →+ X')) : (Fin 8 → X) →+ X' where
  toFun y := ∑ v, c v (y v)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem e8data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have hpG : ∀ v, ∃ F : G' ⟶ G, IsMonHom F ∧
      (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := by
    intro v
    haveI := hpr v
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose pG hpGm hpGg using hpG
  have hgen : ∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    rw [hpGg v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose c hc using fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hR G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  have hbij := (characters_eighthPower_elementaryMatrices R hR hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hgen c hc).1
  let Φ := AddEquiv.ofBijective (sumChars c) hbij
  let Sm := matAddEquiv (M := D.toPre.X) (W + W.transpose) hW.2
  refine ⟨pG, c, Φ.symm.trans Sm.symm, hpGm, hgen, hc, fun y => ?_⟩
  have h1 : Sm ((Φ.symm.trans Sm.symm) y) = Φ.symm y := by simp
  have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [← h1] at h2
  exact h2

end GlobalTheory.Poinc.Eq8
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroupsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  first | exact @GlobalTheory.Poinc.Eq8.e8data | exact GlobalTheory.Poinc.Eq8.e8data | (intros; apply GlobalTheory.Poinc.Eq8.e8data <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Lattice

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum ϖ β hs hp hτ y r hr
  refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e hsum
    ?_ y r hr
  intro v a' b x x' hx hx'
  exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpG v) (c v)
    ((Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom) (hc v)
    (GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum v)
    a' b x x' hx hx'

end GlobalTheory.Poinc.E8Lattice
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  first | exact @GlobalTheory.Poinc.E8Lattice.main | exact GlobalTheory.Poinc.E8Lattice.main | (intros; apply GlobalTheory.Poinc.E8Lattice.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.EighthTorsion
open MonObj

def postcomp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    (T ⟶ G) →* (T ⟶ H) where
  toFun g := g ≫ f
  map_one' := by simp
  map_mul' a b := by simp [MonObj.mul_comp]

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (l : List (T ⟶ G)) : l.prod ≫ f = (l.map (· ≫ f)).prod :=
  (map_list_prod (postcomp (T := T) f) l)

theorem zpow_comp' {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (g : T ⟶ G) (n : ℤ) : (g ^ n) ≫ f = (g ≫ f) ^ n :=
  map_zpow (postcomp (T := T) f) g n

theorem ident_pow {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε)
    (A8 : PolAV (Sp (FractionRing T.V))) (pA : IsPowPolAV A8 T.A 8) :
    ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ φ.hom ≫ pA.pr a = ((List.finRange 8).map fun b => (φ.hom ≫ pA.pr b) ^ E a b).prod := by
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL, hε⟩ := hD
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  have hφp' : ∀ a, φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
      rw [hφp' a, Over.comp_left, Category.assoc, hee]
    have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
    obtain ⟨w', hw'⟩ := T.lb
    have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)
    have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
      (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
    have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
        fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
      funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
    rw [hm] at i₁
    exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
      (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  · intro E a
    haveI := he
    rw [hφp' a, ← Category.assoc, hε E a, prod_comp, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, hφp' b]
    exact zpow_comp' e.hom (pr b) (E a b)

theorem exists_proj {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε) :
    ∃ pr : Fin 8 → (P.A ⟶ T.A.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp (FractionRing T.V))) (y : Fin 8 → (T' ⟶ T.A.A)), ∃! z : T' ⟶ P.A, ∀ a, z ≫ pr a = y a) ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ pr a = (List.ofFn fun b => pr b ^ E a b).prod := by
  obtain ⟨A8, pA, -⟩ := GlobalTheory.exists_powPolAV _ T.A 8
  obtain ⟨φ, hφ, hL, hε⟩ := ident_pow F W T P ε hD A8 pA
  refine ⟨fun a => φ.hom ≫ pA.pr a, fun a => by have := pA.hom a; infer_instance, fun T' y => ?_, hL,
    fun E a => by rw [List.ofFn_eq_map]; exact hε E a⟩
  refine ⟨pA.lim.lift (Fan.mk T' y) ≫ φ.inv, fun a => ?_, fun z hz => ?_⟩
  · rw [Category.assoc, φ.inv_hom_id_assoc]
    exact pA.lim.fac (Fan.mk T' y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    exact pA.lim.uniq (Fan.mk T' y) _ fun a => (Category.assoc _ _ _).trans (hz a.as)

theorem tau_coord {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (a b' : T.D.toPre.X)
    (x : (FractionRing T.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord T.D.toPre a b' x) :
    ∃ u : T.Vˣ, (x : FractionRing T.V) =
      algebraMap T.V (FractionRing T.V) (u : T.V) * algebraMap T.V (FractionRing T.V) T.ϖ ^ (T.β a b') := by
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre (a + b')
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre b'
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main T.V T.D.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨r₁, c₁, e₁⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₁
  obtain ⟨r₂, c₂, e₂⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₂
  obtain ⟨r₃, c₃, e₃⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₃
  obtain ⟨u, hu⟩ := T.mono.tau (fun i y z => by fin_cases i; exact T.symm y z)
    (Fin.forall_fin_one.2 T.irr.ne_zero) c₂ c₃ c₁
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hu
  refine ⟨u₀ * u, ?_⟩
  have key : algebraMap T.V (FractionRing T.V) (u₀ : T.V) * algebraMap T.V (FractionRing T.V) r₁ *
      (algebraMap T.V (FractionRing T.V) r₂)⁻¹ * (algebraMap T.V (FractionRing T.V) r₃)⁻¹ =
      algebraMap T.V (FractionRing T.V) (u₀ : T.V) * (algebraMap T.V (FractionRing T.V) r₁ /
        (algebraMap T.V (FractionRing T.V) r₂ * algebraMap T.V (FractionRing T.V) r₃)) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hu₀, e₁, e₂, e₃, key, hu]
  simp only [Units.val_mul, map_mul]
  ring

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW T P ε hD
  have hCN : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩
  have hB : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, T.char⟩
  have hS : SharpOver F W P T.y := by
    obtain ⟨c, hc, pr, h₁, h₂, h₃, -⟩ := hD
    exact ⟨c, hc, pr, h₁, h₂, h₃⟩
  haveI : IsCommMonObj (powObj T.G 8) := GlobalTheory.PowerExamples.comm_of_pow (powIsPowGrp T.G 8)
  have hG' : IsSemiAbelian (powObj T.G 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ T.G 8 (powIsPowGrp T.G 8) T.semi
  obtain ⟨D', ⟨U'⟩⟩ := GlobalTheory.PowE8.exists_unif_pow8 g n _ _ F W hW T.V hCN T.D T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb P hS
  obtain ⟨pr, hpr, huniv, hL, hε⟩ := exists_proj F W T P ε hD
  obtain ⟨pG, c, e, hpG, hgen, hc, he⟩ := GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr
    huniv hL
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n _ _ F T a ha).le
  refine ⟨powObj T.G 8, inferInstance, inferInstance, hG', D', U', e, fun y => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff _ y).2 (GlobalTheory.PeriodFormCompare.psiIn_top D' y)
    obtain ⟨-, h⟩ := GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc
      e he T.ϖ T.β T.symm hnn (tau_coord T) y r hr
    obtain ⟨v, hv⟩ := h.symm
    exact ⟨v, by rw [mul_comm, hv]; exact hr⟩
  · rintro K _ _ _ m pk pk' x x' E hm h h' rfl
    exact GlobalTheory.T.matrix_acts_on_torsion_labels_alt T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc e he E (ε E)
      (hε E) K m pk pk' x hm h h'

end GlobalTheory.EighthTorsion
end
end
end
