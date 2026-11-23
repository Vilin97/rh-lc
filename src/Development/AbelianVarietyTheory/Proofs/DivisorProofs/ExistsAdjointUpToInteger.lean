module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassMulLeftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleRankComparison

section

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovQF

open CategoryTheory.Limits GlobalTheory.FlagCell

theorem finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (K : Type) [Field K] (y : Sp K ⟶ Y) :
    {x : Sp K ⟶ X | x ≫ f = y}.Finite := by
  have hp : IsFinite (pullback.snd f y) := inferInstance
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f y).isoSpec.inv ≫ pullback.snd f y)
  have h4 : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K Γ(pullback f y, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback f y, ⊤) := h4
  refine (Set.finite_range fun σ : Γ(pullback f y, ⊤) →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pullback f y).isoSpec.inv ≫ pullback.fst f y).subset fun x hx => ?_
  let s : Sp K ⟶ pullback f y := pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (s ≫ (pullback f y).isoSpec.hom)
  have e : φ ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hφ, Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _)
  refine ⟨⟨σ.hom, fun a => congr($e a)⟩, ?_⟩
  show Spec.map σ ≫ _ = _
  rw [hσ, Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

section Sheaves

open GlobalTheory.Twist (resM resM_resM app_resM)

end Sheaves

section Matrices

variable {L : Type} [Field L] {m : ℕ}

end Matrices

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K L : Type} [CommRing R] [Field K] [Field L]

variable {F : Type} [Field F] {e : F ≃+* c.F}

end Frames

section Points

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}
  (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
  {u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB} {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
  {fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)}
  {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {πG : G ⟶ (O.var c).X} {φ : (O.var c).Fn →+* G.functionField}
  {jG : G ⟶ Bg}

end Points

end GlobalTheory.FlagCovQF

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmple

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem memKL_of_lam_geom_eq_zero {K : Type} [Field K] (A : AbVar K) {L : LB A.X.left} (hL : L.IsLB)
    (x : A.Pt) (h : AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0) :
    MemKL A.X L x := by
  set P := ptOver K (AlgebraicClosure K)
  have h1 := congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h
  rw [lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq] at h1
  have h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]
  rw [AbVar.lam, h0, sub_zero] at h1
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A.X L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

end GlobalTheory.AV.AbVar

theorem GlobalTheory.AV.AbVar.finite_lam_eq_zero : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  intro K _ A c ⟨L, hL, ha, hc⟩
  subst hc
  obtain ⟨H, _, i, -, hmono, hfin, -, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha
  have hF := GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
  haveI := hF.to_subtype
  have hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0},
      ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1 := fun x =>
    (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)
  choose z hz using hz
  refine Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ :
    {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_
  intro a b hab
  have e : z a = z b := Over.OverMorphism.ext (congrArg Subtype.val hab)
  exact Subtype.ext ((hz a).symm.trans (e ▸ hz b))
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_mumfordClass_eq_zero_ample : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  first | (exact @GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (exact GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (intros; apply GlobalTheory.AV.AbVar.finite_lam_eq_zero  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClass

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

theorem pull_lam_av {A : AbVar K} (c : Pic A.X.left) {Y Z : Over (Sp K)} (u : Z ⟶ Y) (x y : Y ⟶ A.X) :
    CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) := by
  simp only [AbVar.lam, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem pull_one_eq_zero {A : AbVar K} (c : Pic A.X.left) (Y : Over (Sp K)) :
    CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
  exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
    have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc

theorem exists_phi : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A',
    AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧
      (IsAmpleCls c → IsIsogeny φ) := by
  intro K _ A A' P hP hdim c
  set β : Pic (A.X ⊗ A.X).left := AbVar.lam c (fst A.X A.X) (snd A.X A.X) with hβ
  have hpull : ∀ {Y : Over (Sp K)} (x y : Y ⟶ A.X),
      CechPic.pull (lift x y).left β = AbVar.lam c x y := fun x y => by
    rw [hβ, pull_lam_av, lift_fst, lift_snd]
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ A.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β := by
    intro Y a a' t
    rw [hpull, hpull, hpull]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K A c Y a a' t
  have hnorm : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left β = 0 := by
    rw [hpull, AbVar.lam, _root_.mul_one, pull_one_eq_zero, sub_self, sub_zero]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' A P hP β hadd hnorm
  refine ⟨ψ, hψ, fun hc => ?_⟩
  have hfin : IsFinite ψ.hom.left := by
    refine (GlobalTheory.T.isFinite_iff_finite_ker' K A A' ψ).2 ?_
    have hF := GlobalTheory.T.finite_mumfordClass_eq_zero_ample K A c hc
    refine Finite.of_injective (β := {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K)))
      (snd A.X _ ≫ x) = 0}) (fun x => ⟨x.1, ?_⟩) ?_
    · have hx : x.1 ≫ ψ.hom = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, ptMap_apply] at this
        exact this
      rw [← hpull, hψ, AbDual.pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hx, MonObj.comp_one]
      exact AbDual.evc_one_right hP.isLB hP.zero _
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A A' ψ hdim.symm hfin⟩

end GlobalTheory.AV.AbVar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClassStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hom_to_dual_of_mumfordClass : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A', AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧ (IsAmpleCls c → IsIsogeny φ) := by
  first | (exact @GlobalTheory.AV.AbVar.exists_phi) | (exact GlobalTheory.AV.AbVar.exists_phi) | (intros; apply GlobalTheory.AV.AbVar.exists_phi  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToInteger

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_isAdj : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left),
    IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  intro K _ A B c d hc f
  obtain ⟨A', P, ⟨hP, -⟩, hdim⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  obtain ⟨φ, hφ, hiso⟩ := GlobalTheory.T.exists_hom_to_dual_of_mumfordClass K A A' P hP hdim c
  obtain ⟨n, v, hn, -, -, hvφ⟩ := exists_quasiInverse_isogeny K A A' φ (hiso hc)
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      CechPic.pull (lift (a * a') t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) =
      CechPic.pull (lift a t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) +
      CechPic.pull (lift a' t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) := by
    intro Y a a' t
    simp only [lam_eq, CechPic.pull_lam, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    simp only [← lam_eq]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K B d Y _ _ t
  have hzero : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left
      (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) = 0 := by
    rw [lam_eq, CechPic.pull_lam, lift_snd, CechPic.lam_one_right]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP _ hadd hzero
  have hpow : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (m : ℕ),
      AbDual.evc hP.isLB a (b ^ m) = m • AbDual.evc hP.isLB a b := by
    intro Y a b m
    induction m with
    | zero => rw [pow_zero, zero_smul, AbDual.evc_one_right hP.isLB hP.zero a]
    | succ m ih => rw [pow_succ, GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a, ih, succ_nsmul]
  refine ⟨n, ψ ≫ v, hn, ?_⟩
  have e1 := congrArg (CechPic.pull (lift (fst A.X B.X) (snd A.X B.X ≫ (ψ ≫ v).hom)).left) hφ
  rw [lam_eq, CechPic.pull_lam, AbDual.pull_evc, lift_fst, lift_snd_assoc, lift_snd, ← lam_eq] at e1
  unfold IsAdj
  rw [e1]
  simp only [comp_hom, Category.assoc]
  rw [← comp_hom v φ, hvφ, nsmul_hom, id_hom, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, hpow, ← hψ,
    natCast_zsmul]

end GlobalTheory.AV.AbVar
end
end
end
