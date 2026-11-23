module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveFirstVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorNormalisedZeroSecti

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp
variable {S : Scheme.{0}}
theorem comp_psum_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T T' : Over S} (g : T' ⟶ T) (x : Fin n → (T ⟶ G))
    (I : Finset (Fin n)) : g ≫ psum G x I = psum G (fun k => g ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, toUnit_unique (g ≫ toUnit T) (toUnit T')]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [padd, padd, ← Category.assoc, comp_lift, ih]

theorem psum_one_nrm (G : Over S) [GrpObj G] [IsCommMonObj G] {n : ℕ} {T : Over S} (I : Finset (Fin n)) :
    psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

theorem zeroPair_comp_partialSum_eq_unit (P₀ P : PolAV S) (f g : P₀.A ⟶ P.A) [IsMonHom f] [IsMonHom g] (I : Finset (Fin 2)) :
    zero2 P₀.A ≫ (psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I).left = η[P.A].left := by
  have e : lift η[P₀.A] η[P₀.A] ≫ psum P.A ![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] I = η[P.A] := by
    rw [comp_psum_nrm]
    have : (fun k => lift η[P₀.A] η[P₀.A] ≫ (![fst P₀.A P₀.A ≫ f, snd P₀.A P₀.A ≫ g] : Fin 2 → _) k) =
        fun _ => (1 : 𝟙_ (Over S) ⟶ P.A) := by
      funext k
      fin_cases k <;> simp [IsMonHom.one_hom, Hom.one_def]
    rw [this, psum_one_nrm, Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  exact congrArg (fun q => q.left) e

theorem prod_zpow_nrm {α U : Type} [CommGroup U] (a : U) (e : α → ℤ) (s : Finset α) :
    ∏ i ∈ s, a ^ e i = a ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_nrm (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left]
    (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen) :
    ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J),
      Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  let π := (P₀.A ⊗ P₀.A).hom
  have z2 : zero2 P₀.A ≫ π = 𝟙 S := Over.w (lift η[P₀.A] η[P₀.A])
  have cst : ∀ k, zero2 P₀.A ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k =
      Sum.elim (fun _ => η[P₂.A].left ≫ coprod.inr) (fun _ => η[P₁.A].left ≫ coprod.inl) k := by
    rintro (I | I)
    · show zero2 P₀.A ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] I.down).left ≫ coprod.inr = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
    · show zero2 P₀.A ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] I.down).left ≫ coprod.inl = _
      rw [← Category.assoc, zeroPair_comp_partialSum_eq_unit]; rfl
  have s₁ : ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) = 0 := by decide
  have s₂ : ∑ I : ULift.{0} (Finset (Fin 2)), (-((-1 : ℤ) ^ (2 - I.down.card))) = 0 := by decide
  have hF : FormEq (Sum.elim (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) (fun k => (π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k))
      (Sum.elim (cmpε) (fun k => -cmpε k)) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) cmpε := by
    intro U _ h
    have one : ∏ k, h ((π ≫ zero2 P₀.A) ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k = 1 := by
      simp only [Category.assoc, cst]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cmpε]
      rw [prod_zpow_nrm, prod_zpow_nrm, s₁, s₂, zpow_zero, zpow_zero, _root_.mul_one]
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [DVR.prod_neg _ _ one, inv_one, _root_.mul_one]
  obtain ⟨u', hu', hv⟩ := exists_gen (join_isLB P₁.isLB P₂.isLB) hF
    (LB.mulGen _ _ _ _ _ u (LB.invGen _ _ _ (LB.pullGen _ _ _ u (π ≫ zero2 P₀.A))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ]
  have : (r ≫ zero2 P₀.A) ≫ π ≫ zero2 P₀.A = r ≫ zero2 P₀.A := by
    rw [Category.assoc, ← Category.assoc (zero2 P₀.A), z2]
    exact congrArg (r ≫ ·) (Category.id_comp _)
  rw [this, mul_inv_cancel]

end GlobalTheory.Mum.Two.WeilCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorNormalisedZeroSectiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | exact GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIso

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem exists_cmpGen_of_lbIso (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A)
    (H : LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)
      (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)) :
    ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  obtain ⟨w, hw⟩ := H
  have h₁ := isPart_inl P₁.L P₂.L
  have h₂ := isPart_inr P₁.L P₂.L
  have le : ∀ j : KK → (join P₁.L P₂.L).ι, LB.wchart (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) j ≤
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)).U
        (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => (h₂.mem _ _).1 (Set.mem_iInter.1 hy (.inl k)),
      Set.mem_iInter.2 fun k => (h₁.mem _ _).1 (Set.mem_iInter.1 hy (.inr k))⟩
  let c : ChartPull (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)) (𝟙 _) :=
    { idx := fun j => (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1)
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb (join P₁.L P₂.L) _ _ (𝟙 _) y j j' hj hj').trans ?_
        refine Eq.trans ?_ (gm_div _ _ (𝟙 _) y _ _ ⟨le j hj, le j' hj'⟩).symm
        refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹)
          (gm_linComb P₂.L _ _ (𝟙 _) y _ _ (le j hj).1 (le j' hj').1)
          (gm_linComb P₁.L _ _ (𝟙 _) y _ _ (le j hj).2 (le j' hj').2)).symm
        rw [Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_)
          (Finset.prod_congr rfl fun k _ => (zpow_neg _ _).trans (congrArg (fun u => (u ^ _)⁻¹) ?_))
        · refine Eq.trans ?_ (h₂.g _ (𝟙 _ ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] k.down).left) y _ _
            ((h₂.mem _ _).1 (Set.mem_iInter.1 hj (.inl k))) ((h₂.mem _ _).1 (Set.mem_iInter.1 hj' (.inl k))))
          simp only [cmpφ, Sum.elim_inl, Category.assoc]
        · refine Eq.trans ?_ (h₁.g _ (𝟙 _ ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] k.down).left) y _ _
            ((h₁.mem _ _).1 (Set.mem_iInter.1 hj (.inr k))) ((h₁.mem _ _).1 (Set.mem_iInter.1 hj' (.inr k))))
          simp only [cmpφ, Sum.elim_inr, Category.assoc] }
  exact ⟨cGen c w, cGen_isGen c hw⟩

end GlobalTheory.Mum.Two.WeilCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | exact GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIso

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem cubN_cmp {T : Over S} (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂]
    [IsMonHom g₂] {U : Type} [CommGroup U] (v : (T ⟶ P₀.A) → (T ⟶ P₀.A) → U)
    {θ₁ : (T ⟶ P₁.A) → (T ⟶ P₁.A) → (T ⟶ P₁.A) → U} {θ₂ : (T ⟶ P₂.A) → (T ⟶ P₂.A) → (T ⟶ P₂.A) → U}
    (h₁ : IsCub θ₁) (h₂ : IsCub θ₂)
    (a₁ : ∀ x x' y, v (x * x') y * θ₁ (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) =
      θ₂ (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (v x y * v x' y))
    (a₂ : ∀ x y y', v x (y * y') * θ₁ (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) =
      θ₂ (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (v x y * v x y'))
    {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN θ₁ k 1 (x ≫ f₁) (y ≫ g₁) = cubN θ₂ k 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ k ∧
      cubN θ₁ k 1 (y ≫ g₁) (x ≫ f₁) = cubN θ₂ k 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ k := by
  have first : ∀ n : ℕ, v (x ^ n) y * cubN θ₁ n 1 (x ≫ f₁) (y ≫ g₁) =
      v 1 y * (cubN θ₂ n 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₁ (x ^ n) x y
      rw [MonObj.pow_comp, MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, v x (y ^ n) * cubN θ₁ n 1 (y ≫ g₁) (x ≫ f₁) =
      v x 1 * (cubN θ₂ n 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₂ x (y ^ n) y
      rw [MonObj.pow_comp, MonObj.pow_comp, h₁.s01 (x ≫ f₁), h₁.s12 _ (x ≫ f₁), h₂.s01 (x ≫ f₂),
        h₂.s12 _ (x ≫ f₂)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨mul_left_cancel a, mul_left_cancel b⟩

theorem isRatio_cmp (hG : GlobalFnsSt) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A)
    (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    {r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} {hr₁ : r₁.IsGen} (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩)
    {r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} {hr₂ : r₂.IsGen} (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩)
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1)
    {T : Over S} {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : WeilCube.IsRatio c₁ k (x ≫ f₁) (y ≫ g₁) e) : WeilCube.IsRatio c₂ k (x ≫ f₂) (y ≫ g₂) e := by
  intro T' ρ z J₂ hJ₂
  obtain ⟨J₁, hJ₁, -⟩ := exists_good P₁.L P₁.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  obtain ⟨J, hJ, e₁, e₂⟩ := exists_good_join P₁.isLB P₂.isLB hJ₁ hJ₂
  have hx' : (ρ ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have hy' : (ρ ≫ y) ^ k = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have q₁ : Good P₁.L z (rl J) := (isPart_inl P₁.L P₂.L).good hJ
  have q₂ : Good P₂.L z (rr J) := (isPart_inr P₁.L P₂.L).good hJ
  obtain ⟨a, b⟩ := cubN_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (fun a b => val u (lift a b).left z J) (isCub_cubV c₁ q₁)
    (isCub_cubV c₂ q₂) (fun x x' y => GlobalTheory.T.weilComparisonGenerator_additive_first_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x x' y)
    (fun x y y' => GlobalTheory.T.weilComparisonGenerator_additive_second_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x y y') hx' hy'
  rw [e₁, e₂] at a b
  simp only [Category.assoc] at a b
  have h := he T' ρ z J₁ hJ₁
  rw [a, b, ← _root_.mul_assoc] at h
  exact mul_right_cancel h

end GlobalTheory.Mum.Two.WeilCmp


open GlobalTheory.Mum.Two.WeilCmp in
theorem GlobalTheory.Mum.Two.weilIs_iff_of_lbIso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  intro S _ P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ _ _ hw F _ p k x y hx hy c
  have hL := GlobalTheory.allSixLaws.1
  haveI : Nonempty P₁.A.left := ⟨(x ≫ f₁).left (⊥ : PrimeSpectrum F)⟩
  haveI : Nonempty P₂.A.left := ⟨(x ≫ f₂).left (⊥ : PrimeSpectrum F)⟩
  obtain ⟨r₁, hr₁, ⟨c₁⟩⟩ := PolAV_exists_cubical hL.cube P₁
  obtain ⟨r₂, hr₂, ⟨c₂⟩⟩ := PolAV_exists_cubical hL.cube P₂
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso S P₀ P₁ P₂ f₁ g₁ f₂ g₂ hw
  obtain ⟨u, hu, hn⟩ := GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection S P₀ P₁ P₂ f₁ g₁ f₂ g₂ u₀ hu₀
  have hx₁ : (x ≫ f₁) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₁ : (y ≫ g₁) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx₂ : (x ≫ f₂) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₂ : (y ≫ g₂) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨e₀, he₀⟩ := WeilCube.exists_isRatio c₁ k (x ≫ f₁) (y ≫ g₁) hx₁ hy₁
  have he₂ := isRatio_cmp P₀ P₁ P₂ hL.globalFns f₁ g₁ f₂ g₂ c₁ c₂ u hu hn hx hy he₀
  exact (WeilCube.weilIs_iff c₁ hL.globalFns P₁.isAb hx₁ hy₁ he₀ c).trans
    (WeilCube.weilIs_iff c₂ hL.globalFns P₂.isAb hx₂ hy₂ he₂ c).symm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.commutator_pairing_eq_of_mumford_bundle_iso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  first | exact @GlobalTheory.Mum.Two.weilIs_iff_of_lbIso | exact GlobalTheory.Mum.Two.weilIs_iff_of_lbIso | (intros; apply GlobalTheory.Mum.Two.weilIs_iff_of_lbIso <;> assumption)
end
end
