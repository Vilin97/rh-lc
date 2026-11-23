module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginMemIdealPowOfVanishesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginPullbackDegenerationStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.AdicSum


open Classical in
theorem sum_sub_sum_mem {R : Type} [CommRing R] (J : Ideal R) {X : Type} (v : X → R)
    (S T : Finset X) (hS : ∀ α ∉ S, v α ∈ J) (hT : ∀ α ∉ T, v α ∈ J) :
    ∑ α ∈ S, v α - ∑ α ∈ T, v α ∈ J := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]
  exact J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2)
    (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)

theorem exists_adic_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) →
    ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) →
      s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  intro R _ _ _ hR X v hfin
  have hC : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  have hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite := fun n =>
    (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) =>
      hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)
  let F : ℕ → Finset X := fun n => (hfin' n).toFinset
  have hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n := by
    intro n α hα
    by_contra h
    exact hα ((hfin' n).mem_toFinset.2 h)
  let f : ℕ → R := fun n => ∑ α ∈ F n, v α
  have hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := (hC.toIsPrecomplete).prec (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    exact sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m)
      fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))
  refine ⟨L, fun e S hS => ?_⟩
  have h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1) := by
    have := hL (e + 1)
    rwa [SModEq.sub_mem, hsm] at this
  have h2 := sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS
  have : L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

end GlobalTheory.Mum.AdicSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_adicSum_null_family_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) → ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) → s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  first | exact @GlobalTheory.Mum.AdicSum.exists_adic_sum | exact GlobalTheory.Mum.AdicSum.exists_adic_sum | (intros; apply GlobalTheory.Mum.AdicSum.exists_adic_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPow

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem cst_id_eq_stalkOf {W : Type} [CommRing W] (z : Sp W) (a : W) : cst (𝟙 (Sp W)) z a = stalkOf z a :=
  gs_eq (𝟙 _) z ⊤ trivial _


open GlobalTheory.ExpansionValueZero in
theorem expandsAt_origVal : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro W _ _ _ D' A G _ _ U k e σ' f' w hw hE
  classical
  choose a ha using fun α => exists_value D'.toPre k α (f' α)
  obtain rfl : w = a := funext fun α => stalkOf_injective (cpt W) (by
    choose J hJ using fun ψ : Sp W ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (ψ (cpt W))
    have h₁ := ha α _ (𝟙 (Sp W)) (cpt W) J hJ
    have h₂ := hw α (cpt W) J hJ
    rw [cst_id_eq_stalkOf] at h₁
    rw [← Units.val_pow_eq_pow_val] at h₂
    have h₃ : sval (f' α) (𝟙 (Sp W) ≫ eSec D'.toPre.P.A) (cpt W) J = sval (f' α) (unitW D'.toPre.P.A) (cpt W) J :=
      congrArg (fun q => sval (f' α) q (cpt W) J) (Category.id_comp (unitW D'.toPre.P.A))
    exact (Units.mul_left_inj _).1 (h₂.symm.trans (h₃.symm.trans h₁)))
  obtain ⟨x, hx⟩ := exists_coeff (A := W) U.LG.isLB σ' (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (DVR.powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (J), Good U.LG.L z J →
      sval σ' (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun Z r z J hJ => (hx Z r z J hJ).trans (by rw [DVR.val_pow])
  obtain ⟨S, hS⟩ := value_sub_sum_mem U e k σ' f' hE x hx' w ha
  refine ⟨S, fun y hy => ?_, fun J' hJ' => ⟨x - ∑ α ∈ S, w α, hS S le_rfl, ?_⟩⟩
  · have h := Ideal.sub_mem _ (hS S le_rfl) (hS (insert y S) (Finset.subset_insert _ _))
    rw [Finset.sum_insert hy] at h
    convert h using 1
    ring
  · have h₁ := hx' _ (𝟙 (Sp W)) (cpt W) J' hJ'
    rw [cst_id_eq_stalkOf, Units.val_pow_eq_pow_val] at h₁
    rw [add_sub_cancel]
    exact (congrArg (fun q => sval σ' q (cpt W) J') (Category.id_comp (unitW G))).symm.trans h₁

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPowStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.expansion_originValues_sum_modPow : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  first | exact @GlobalTheory.Mum.expandsAt_origVal | exact GlobalTheory.Mum.expandsAt_origVal | (intros; apply GlobalTheory.Mum.expandsAt_origVal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitRigidifiedValueAtOrigin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem stalkOf_closedPoint_isUnit {W : Type} [CommRing W] [IsLocalRing W] (v : W)
    (h : IsUnit (stalkOf (closedPoint W) v)) : IsUnit v := by
  have e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom := by
    unfold stalkOf
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext x
    simp
  rw [e] at h
  exact (isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h

theorem isUnit_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  intro R _ _ _ D k α b v hv hmem
  have hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j) := by
    unfold nonzeroLocus at hmem
    simpa [TopologicalSpace.Opens.mem_iSup] using hmem
  obtain ⟨j, hj⟩ := hmem'
  have hjU := D.P.A.left.basicOpen_le (b.f j) hj
  have hu := (Scheme.mem_basicOpen _ _ _ hjU).1 hj
  obtain ⟨J, hJ, -⟩ := exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hsv := hv (closedPoint R) J hJ
  have e1 := sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU
  have hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j)) := by
    rw [gs_eq _ _ _ hjU]
    have e2 := Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)
    exact e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom
  have hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J) := by
    show IsUnit (gs _ _ _ _)
    rw [e1]
    exact (Units.isUnit _).mul hg
  rw [hsv] at hs
  exact stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitRigidifiedValueAtOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isUnit_rigidifiedValueAtOrigin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  first | exact @GlobalTheory.Mum.isUnit_origVal | exact GlobalTheory.Mum.isUnit_origVal | (intros; apply GlobalTheory.Mum.isUnit_origVal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAdicSumOriginValuesIntegralFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_origin_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro R _ _ _ hB D C k hk b₀ hb₀ F₀ hL
  choose v hv using fun α => GlobalTheory.T.exists_rigidifiedValueAtOrigin R D.toPre k α (F₀.f α)
  have hvm : ∀ α e, VanMod (maximalIdeal R) (F₀.f α) e → v α ∈ maximalIdeal R ^ (e + 1) :=
    fun α e h => GlobalTheory.T.rigidifiedValueAtOrigin_mem_idealPow_of_vanishes R _ D.toPre k α (F₀.f α) (v α) e (hv α) h
  have hfin : ∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite := fun e =>
    (F₀.small e).subset fun α h h' => h (hvm α e h')
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adicSum_null_family_complete_local R hB D.toPre.X v hfin
  refine ⟨s, ?_, ?_⟩
  · have hv0 : IsUnit (v 0) := by
      have h0 := hv 0
      rw [hL.1] at h0
      exact GlobalTheory.T.isUnit_rigidifiedValueAtOrigin R D.toPre k 0 b₀ (v 0) h0 hb₀
    have h1 : s - v 0 ∈ maximalIdeal R := by
      have := hs 0 {0} (fun α hα => hvm α 0 (hL.2 α (by simpa using hα)))
      simpa using this
    by_contra hn
    have hs' : s ∈ maximalIdeal R := (mem_maximalIdeal s).2 hn
    have : v 0 ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hs' h1
      simpa using this
    exact ((mem_maximalIdeal _).1 this) hv0
  · intro W _ _ _ T σ' f' hP hE J' hJ'
    have hw : ∀ x, OrigVal T.D'.toPre (f' x) (T.φ (v (T.hD.xe x))) := fun x =>
      GlobalTheory.T.rigidifiedValueAtOrigin_pullback_degeneration R W T.φ D.toPre T.D'.toPre T.hD k x (F₀.f (T.hD.xe x)) (f' x) (v (T.hD.xe x)) (hP x) (hv _)
    haveI : IsLocalHom T.φ := T.loc
    have hmap : ∀ e, (maximalIdeal R ^ (e + 1)).map T.φ ≤ maximalIdeal W ^ (e + 1) := fun e => by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ _
      refine Ideal.map_le_iff_le_comap.2 fun x hx => (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal x).1 hx (isUnit_of_map_unit T.φ x hu)
    have step : ∀ e : ℕ, ∃ c ∈ maximalIdeal W ^ (e + 1),
        sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s + c) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
      intro e
      obtain ⟨S, hS, hc⟩ := GlobalTheory.T.expansion_originValues_sum_modPow W T.D' T.A T.G T.U.toUnifPre k e σ' f' _ hw (hE e)
      obtain ⟨c, hcm, heq⟩ := hc J' hJ'
      classical
      let S1 : Finset D.toPre.X := S.map T.hD.xe.toEquiv.toEmbedding
      let S2 : Finset D.toPre.X := S1 ∪ (hfin e).toFinset
      have h2 := hs e S2 (fun α hα => by
        by_contra h
        exact hα (Finset.mem_union_right _ ((hfin e).mem_toFinset.2 h)))
      have hsum1 : ∑ x ∈ S, T.φ (v (T.hD.xe x)) = T.φ (∑ α ∈ S1, v α) := by

        simp [S1, map_sum]
      have hdiff : T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α) ∈ maximalIdeal W ^ (e + 1) := by

        rw [← map_sub, ← Finset.sum_sdiff (Finset.subset_union_left : S1 ⊆ S2), add_sub_cancel_right, map_sum]
        refine Ideal.sum_mem _ fun α hα => ?_
        have hα1 : α ∉ S1 := (Finset.mem_sdiff.1 hα).2
        have := hS (T.hD.xe.symm α) (fun hx => hα1 (by
          simp only [S1, Finset.mem_map_equiv]
          simpa using hx))
        simpa using this
      have h2' : T.φ s - T.φ (∑ α ∈ S2, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub]; exact hmap e (Ideal.mem_map_of_mem _ h2)
      refine ⟨c - (T.φ s - T.φ (∑ α ∈ S2, v α)) - (T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α)),
        Ideal.sub_mem _ (Ideal.sub_mem _ hcm h2') hdiff, ?_⟩
      rw [heq, hsum1]
      congr 2
      ring
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 T.cdvr).1
    choose c hc heq using step
    have hce : ∀ e, c e = c 0 := fun e => by
      have := (heq e).symm.trans (heq 0)
      have hu := (Units.isUnit ((val T.U.LG.rig (idW W) (cpt W) J') ^ k))
      rw [Units.val_pow_eq_pow_val] at hu
      have := hu.mul_right_cancel this
      apply add_left_cancel (a := T.φ s)
      apply stalkOf_injective (cpt W)
      exact this
    have h0 : c 0 = 0 := by
      have hm : c 0 ∈ ⨅ n : ℕ, maximalIdeal W ^ n := Submodule.mem_iInf _ |>.2 fun n => by
        rcases n with _ | n
        · simp
        · rw [← hce n]; exact hc n
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W) (maximalIdeal.isMaximal W).ne_top, Submodule.mem_bot] at hm
    rw [heq 0, h0, add_zero]

end GlobalTheory.Mum
end
end
end
