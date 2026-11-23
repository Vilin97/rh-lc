module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonposStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpenStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonposStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlaces

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFrameAndLocalFramesAllPlacesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  first | exact @GlobalTheory.Nef.exists_frame_locFrames | exact GlobalTheory.Nef.exists_frame_locFrames | (intros; apply GlobalTheory.Nef.exists_frame_locFrames <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosed

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem exists_isGenOver (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (x : Sp K ⟶ C), IsGenOver k x := by
  have := LieSemineg.isIntegral_curve h.1 h.2.2
  let x : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
  let φ : CommRingCat.of k ⟶ CommRingCat.of C.functionField := Spec.preimage (x ≫ strHom k C)
  refine ⟨C.functionField, inferInstance, φ.hom.toAlgebra, x, h, isGen_fromSpecStalk C, ?_⟩
  exact (Spec.map_preimage (x ≫ strHom k C)).symm

theorem semiNeg_lie_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  intro k _ _ _ C _ h G _ hG W r hW i hi
  obtain ⟨K, _, _, x, hx⟩ := exists_isGenOver k C h
  obtain ⟨V₀, s, g, hV, hs, hg, hl⟩ := GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces k K C x hx W r hW
  have hL := GlobalTheory.T.lie_subsheaf_lines_degree_nonpos k K C x hx G hG W r i hi V₀ s g hV hs hg hl
  have hd := GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound r k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) g hg 0 hL
  rw [mul_zero] at hd
  exact GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos k K C x hx W r hW V₀ s g hV hs hg hl (by exact_mod_cast hd)

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSheafSemiAbelianSemiNegOfIsAlgClosedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  first | exact @GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | exact GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | (intros; apply GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeOfNeron

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := GlobalTheory.T.semiNegative_descends_fieldExtension_curve k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
end
end
end
