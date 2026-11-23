module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGradedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFieldsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFramesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RadicalPrincipalIdealsStayRadicalFlagComponentStatement
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumfordStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentRefinesLieFramesGraded

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.BaseRefine

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', hG⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  exact ⟨E', φ, ⟨fun _ => Nat.zero_le _, hφ, hsub,
    GlobalTheory.T.radical_principal_ideals_stay_radical_flag_component E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩, hG⟩

end GlobalTheory.ShFam.BaseRefine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentRefinesLieFramesGradedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  first | exact @GlobalTheory.ShFam.BaseRefine.main | exact GlobalTheory.ShFam.BaseRefine.main | (intros; apply GlobalTheory.ShFam.BaseRefine.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlagStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpace_component_unique_point_each_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  first | exact @GlobalTheory.CarryAll.carries_everywhere | exact GlobalTheory.CarryAll.carries_everywhere | (intros; apply GlobalTheory.CarryAll.carries_everywhere <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_base_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∃ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn), (j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) ∧ IsLieBase e (Φ.C k) X j f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.T.exists_variety_connectedComponent_genericFibre E H Dw l Xo c O β T.Z F e T.smooth (Φ.C k).Y (Φ.C k).π (Φ.C k).π_str
  let f : (Φ.C k).Y.X ⟶ X.X := IsOpenImmersion.lift j (Φ.C k).π hr
  have hf : f ≫ j = (Φ.C k).π := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f₀, Eb, A₀, hT⟩ := GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β T.Z F e X j hj
  have hcar := GlobalTheory.T.flagSpace_component_unique_point_each_flag E H Dw l Xo c O β T.Z F e σ _ U Φ k X j hoi hj f hf
  obtain ⟨E', φ, hR, hG⟩ := GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded E H Dw l Xo c O β T.Z F e (Φ.C k) X j hoi hj f hf f₀ Eb A₀ hT
    (fun K _ _ χ x hx g => hcar K χ x hx g)
  exact ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, ⟨hoi, hf, hT⟩, hR, hG⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodBase

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_goodBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp),
      ∃ (X : Var F) (Eb : Fr (ratOf X) Dw.mult 0) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult)
        (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn) (f : (Φ.C k).Y.X ⟶ X.X) (Ob : X.X.Opens)
        (Hm : Mat Dw.mult X.Fn → GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → Mat Dw.mult ℂ),
        Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) ∧ IsMetricOn Eb Ob Hm ∧
          IsGood Eb Ob Hm ∧
          ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
            antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^
                (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult →
              HasChernIntegral Eb Ob Hm R
                (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, hB, hR, hG⟩ := GlobalTheory.LieBase.exists_base_of_flagCpt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  refine ⟨X, Eb, E', φ, f, openPart j, lieGram e U hj f₀ A₀, hR, hG,
    GlobalTheory.LieBase.isMetricOn_lieGram E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    fun la R h => ?_⟩
  convert GlobalTheory.T.hodgeMetric_chernIntegral_eq_covolume_mul_flagDegree E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hB la R h using 3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfInterLwInterPoly

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Member

theorem selfInter_Lw_interPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) (la : GlobalTheory.AllWt.Weight Dw),
    ((C.Y.inter (fun _ => C.Lw la) : ℤ) : ℝ) =
      C.Y.interPoly (fun x : Root Dw.mult => C.gr x.1 x.2)
        ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ C.Y.dim) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C la
  rw [← Fin.prod_const]
  have h := C.Y.interPoly_prod_sum (fun x : Root Dw.mult => C.gr x.1 x.2)
    (fun _ x => -(GlobalTheory.AllWt.exOf Dw la 0 (some x)))
  push_cast at h
  rw [h]
  congr 2
  funext i
  simp [FlagCpt.Lw, FlagCpt.LEx, Finset.sum_neg_distrib]

end GlobalTheory.Member
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality := by
  first | exact @GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | exact GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | (intros; apply GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement

section

@[expose] public section

section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem PublishedHodgeBundleTheorems.toClassicalTheorems : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil
end GlobalTheory.CovTop
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.covering_topology_refinement : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := by
  first | exact @_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | exact _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | (intros; apply _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems <;> assumption)
end
end
end
