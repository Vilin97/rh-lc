module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CohomologyPresheafFunctorMapAppApply
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSections

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl


open Classical in
def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add (f := _), add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSectionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a := by
  first | exact @GlobalTheory.Cartier.exists_ratOn_twist | exact GlobalTheory.Cartier.exists_ratOn_twist | (intros; apply GlobalTheory.Cartier.exists_ratOn_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (GlobalTheory.toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplitStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.mayer_vietoris_sections_split : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  first | exact @GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | exact GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | (intros; apply GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.rational_function_split_regular_divisor : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens), Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) → ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) → ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧ ∀ y ∈ W₂, D.RegularAt y h₂ := by
  first | exact @GlobalTheory.ratsec_split_of_H1 | exact GlobalTheory.ratsec_split_of_H1 | (intros; apply GlobalTheory.ratsec_split_of_H1 <;> assumption)
end
end
