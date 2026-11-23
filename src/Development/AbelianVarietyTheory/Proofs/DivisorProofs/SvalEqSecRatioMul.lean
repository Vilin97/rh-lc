module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitSvalIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel

section

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Calc

variable {Y W W' Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {ψ : K → (W ⟶ Y)} {ψ' : K → (W' ⟶ Y)}
  {ε ε' : K → ℤ} {r : Z ⟶ W} {r' : Z ⟶ W'}

end Calc

section Image

variable {Y G B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] (q : G ⟶ B) {φ : K → (B ⟶ Y)} {φ' : K → (G ⟶ Y)}
  {ε ε' : K → ℤ}

variable {q} {x : LB.Gen (LB.LinComb L φ' ε')} {V : B.Opens}


end Image

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

section One

variable [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (hL : L.IsLB) {φ : K → (B.left ⟶ Y)} {φ' : K → (G.left ⟶ Y)}
  (hφ : ∀ k, φ' k = q.left ≫ φ k) {x : LB.Gen (LB.LinComb L φ' ε')} (hx : x.IsGen) {χ : X} (hw : WtGen i x χ)
include hi hL hφ hx hw


end One

section All

variable [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] (hL : L.IsLB) (hε : ∀ k, ε' k = -ε k)
  {φ : X → K → (B.left ⟶ Y)} {φ' : X → K → (G.left ⟶ Y)} (hφ : ∀ χ k, φ' χ k = q.left ≫ φ χ k)
  {x : ∀ χ, LB.Gen (LB.LinComb L (φ' χ) ε')} (hx : ∀ χ, (x χ).IsGen) (hw : ∀ χ, WtGen i (x χ) χ)
include hL hε hφ hx hw


end All

end Group

end GlobalTheory.GtCoordCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SvalEqSecRatioMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermWeight

theorem sval_eq_secRatio_mul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) (hz : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (GlobalTheory.ProjSpace.secRatio a b) * sval a r z J := by
  have hm : r z ∈ nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (GlobalTheory.ProjSpace.secRatio_on a b (fun k => J (r ≫ φ k))
    (W := nonzeroLocus a ⊓ LB.wchart L φ (fun k => J (r ≫ φ k))) inf_le_left inf_le_right)
  exact (gs_res r z inf_le_right hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z inf_le_left hm _) (gs_res r z inf_le_right hm _))))

theorem isWt_secRatio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), (∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J → val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J) → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ (k : ℕ) (α : D.X) (b₀ : D.SecB k 0) (b : D.SecB k α) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → GlobalTheory.UU.IsWt i (nonzeroLocus τ₀) (GlobalTheory.ProjSpace.secRatio τ₀ τ) α := by
  intro R _ _ D Y i hi hk k α b₀ b τ₀ τ h₀ h
  have := Y.isMonHom_q
  refine GlobalTheory.GtCoordCompare.isWt_of_gs fun Z t g hg z => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have hq : (((t ≫ i) * g) ≫ Y.q).left = (g ≫ Y.q).left := GlobalTheory.GtCoordCompare.act_comp hk.w t g
  have z₁ : val ((Y.Φ Z ((t ≫ i) * g)).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have z₂ : val ((Y.Φ Z g).s 0) (𝟙 _) z J = 1 := GlobalTheory.TorusModel.cv_zero _ hJ
  have e₀ : sval τ₀ ((t ≫ i) * g).left z J = sval τ₀ g.left z J := by
    rw [h₀ Z _ z J hJ, h₀ Z g z J hJ, hq, z₁, z₂]
  have e : sval τ ((t ≫ i) * g).left z J =
      (gm t.left z ⊤ (charUnit (Sp R) D.X α)).val * sval τ g.left z J := by
    rw [h Z _ z J hJ, h Z g z J hJ, hq, hi α Z t g z J hJ, Units.val_mul, mul_left_comm]
  have hz : g.left z ∈ nonzeroLocus τ₀ := hg (Set.mem_univ z)
  have hu : IsUnit (sval τ₀ g.left z J) := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).2 hz
  have hz' : ((t ≫ i) * g).left z ∈ nonzeroLocus τ₀ := (TermLocus.isUnit_sval_iff τ₀ _ z hJ).1 (e₀ ▸ hu)
  refine hu.mul_right_cancel ?_
  rw [_root_.mul_assoc, ← sval_eq_secRatio_mul τ₀ τ g.left z hJ hz, ← e, sval_eq_secRatio_mul τ₀ τ _ z hJ hz', e₀]

end GlobalTheory.Mum.TermWeight
end
end
end
