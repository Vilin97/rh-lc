module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialAdditiveFamilyKilledByIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupSchemeStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroupStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Connected

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernel

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualKernel

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem evc_ker_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    evc hP (fst T B ≫ x) (snd T B) = 0 ↔ evc hP (snd B T ≫ x) (fst B T) = 0 := by
  constructor
  · intro h
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) h
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  · intro h
    have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) h
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem evc_ker_mul {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x y : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) (hy : evc hP (fst T B ≫ y) (snd T B) = 0) :
    evc hP (fst T B ≫ (x * y)) (snd T B) = 0 := by
  rw [MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, hy, add_zero]

theorem evc_ker_one {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) (T : Over S) :
    evc hP (fst T B ≫ (1 : T ⟶ A)) (snd T B) = 0 := by
  rw [MonObj.comp_one]
  exact hA.evc_one hP _

theorem evc_ker_inv {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) : evc hP (fst T B ≫ x⁻¹) (snd T B) = 0 := by
  have e := evc_ker_one hP hA T
  rw [← mul_inv_cancel x, MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, zero_add] at e
  exact e

end GlobalTheory.DualKernel

namespace GlobalTheory.DualKernel

theorem exists_closed_subgroup_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P →
    ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧
      Triv (ev P (fst N B ≫ i) (snd N B)) ∧
      ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  intro K _ _ A B _ _ P hA hB hD
  have hP := hD.isLB
  have hs : (swap P).IsLB := pull_isLB hP _
  have ht : (LB.triv (B ⊗ A).left).IsLB := LB.isLB_triv _
  have h0 : ∀ (Y : Over (Sp K)) (b : Y ⟶ B) (a : Y ⟶ A), evc ht b a = 0 := fun _ _ _ ↦ map_zero _
  have hN : Fam B (swap P) := ⟨hs, isDual_isAdditive_swap _ A B P hB hD⟩
  have hN' : Fam B (LB.triv (B ⊗ A).left) :=
    ⟨ht, (isAdditive_iff ht).2 fun _ _ _ _ ↦ by simp only [h0, add_zero]⟩
  haveI := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨N, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp K) B A hB (swap P) _ hN hN'
  have key : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      evc hP (fst T B ≫ x) (snd T B) = 0 ↔ ∃ z : T ⟶ N, z ≫ i = x := fun T x ↦ by
    rw [← hG, same_iff hs ht, h0, evc_swap hP hs, evc_ker_iff]
  have hK : ∀ (T : Over (Sp K)) (z : T ⟶ N), evc hP (fst T B ≫ z ≫ i) (snd T B) = 0 :=
    fun T z ↦ (key T _).2 ⟨z, rfl⟩
  haveI : Mono i.left := inferInstance
  haveI : Mono i := Over.mono_of_mono_left i
  have hl : ∀ {T : Over (Sp K)} (x : T ⟶ A), evc hP (fst T B ≫ x) (snd T B) = 0 →
      ∃ z : T ⟶ N, z ≫ i = x := fun x h ↦ (key _ x).1 h
  obtain ⟨o, ho⟩ := hl (η[A] : 𝟙_ (Over (Sp K)) ⟶ A) (by
    have e := evc_ker_one hP hD.additive (𝟙_ (Over (Sp K)))
    rwa [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at e)
  obtain ⟨m, hm⟩ := hl ((i ⊗ₘ i) ≫ μ[A]) (by
    have e := evc_ker_mul hP hD.additive (fst N N ≫ i) (snd N N ≫ i) (hK _ _) (hK _ _)
    rwa [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] at e)
  obtain ⟨n, hn⟩ := hl (i ≫ GrpObj.inv) (by
    have e := evc_ker_inv hP hD.additive i (by simpa using hK N (𝟙 N))
    rwa [Hom.inv_def] at e)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  refine ⟨N, g, i, hg, hi, (triv_ev_iff hP _ _).2 (by simpa using hK N (𝟙 N)), fun T x hx ↦ ?_⟩
  exact (key T x).1 ((triv_ev_iff hP _ _).1 hx)

end GlobalTheory.DualKernel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernelStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closedSubgroupScheme_poincare_left_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧ Triv (ev P (fst N B ≫ i) (snd N B)) ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  first | exact @GlobalTheory.DualKernel.exists_closed_subgroup_ker | exact GlobalTheory.DualKernel.exists_closed_subgroup_ker | (intros; apply GlobalTheory.DualKernel.exists_closed_subgroup_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivialStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  first | exact @GlobalTheory.AbDual.memKL_of_triv_ev_left | exact GlobalTheory.AbDual.memKL_of_triv_ev_left | (intros; apply GlobalTheory.AbDual.memKL_of_triv_ev_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDimField

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' →
    IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g A'.hom := by
  intro K _ _ A A' _ _ g q hA hA' hfin hsurj hg
  have := hA.geomConnected
  have := hA'.geomConnected
  have := hA'.smooth
  have : ConnectedSpace A.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) (𝟙 _) (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected A'.hom (Classical.arbitrary A'.left)
  have hw : q.left ≫ A'.hom = A.hom := Over.w q
  have hg' : SmoothOfRelativeDimension g (q.left ≫ A'.hom) := by rw [hw]; exact hg
  have e := GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := K) q.left A'.hom hg' hm
  subst e
  exact hm

end GlobalTheory.FiniteSurjDimField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelianStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom := by
  first | exact @GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosed

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualKer

theorem finite_of_factor {K : Type} [Field K] {N A H : Over (Sp K)} (i : N ⟶ A) (j : H ⟶ A) (z : N ⟶ H)
    (hz : z ≫ j = i) (hi : IsClosedImmersion i.left) (hj : IsClosedImmersion j.left) (hH : IsFinite H.hom) :
    IsFinite N.hom := by
  have e : z.left ≫ j.left = i.left := by rw [← Over.comp_left, hz]
  haveI : IsClosedImmersion (z.left ≫ j.left) := e ▸ hi
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left j.left
  have : N.hom = z.left ≫ H.hom := (Over.w z).symm
  rw [this]; infer_instance

theorem leftKer_eq_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  intro K _ _ A B _ _ g P hA hB hgA hgB hP T x hx
  obtain ⟨N, _, i, hi, hci, hNt, hfac⟩ := GlobalTheory.T.exists_closedSubgroupScheme_poincare_left_kernel K A B P hA hB hP
  obtain ⟨L, H, _, j, hL, -, -, -, hcj, hH, hKL⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨z, hz⟩ := (hKL N i).1 (GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial K A B P L hA hB hP hL N i hNt)
  have hfin : IsFinite N.hom := finite_of_factor i j z hz hci hcj hH
  haveI : Mono i.left := inferInstance
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (by simpa using (inferInstance : Mono i.left))
  obtain ⟨A', _, hA', q, hq, hqf, hqfl, hqs, hpb⟩ := GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme K A hA N i hi hmono hfin
  have hgA' := GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety K A A' g q hA hA' hqf hqs hgA
  obtain ⟨P', hP', hP'a, hP'i⟩ := GlobalTheory.T.poincareBundle_descends_quotient_finiteSubgroup K A A' B N P i q hA hA' hB hP hi hq hqf hqfl hqs hpb hNt
  have hi1 : i = 1 := by
    by_contra hne
    obtain ⟨T', M, hM, hMa, hMq, hMn⟩ := GlobalTheory.T.exists_nontrivial_additive_family_killed_by_isogeny K A A' N i q hA hA' hi hq hfin hqf hqfl hqs hpb hne
    exact hMn (GlobalTheory.T.additiveFamily_trivial_of_quotient_pullback_trivial K A A' B g P P' q hA hA' hB hgA' hgB hP hq hP' hP'a hP'i T' M hM hMa hMq)
  obtain ⟨w, rfl⟩ := hfac T x hx
  rw [hi1, MonObj.comp_one]

end GlobalTheory.DualKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualPoincare_left_kernel_trivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  first | exact @GlobalTheory.DualKer.leftKer_eq_one | exact GlobalTheory.DualKer.leftKer_eq_one | (intros; apply GlobalTheory.DualKer.leftKer_eq_one <;> assumption)
end
end
