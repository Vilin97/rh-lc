module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibreStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigRescale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem exists_rescale_rig : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  intro A _ L g u rig hL hr
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp [eSec]
  obtain ⟨j₀, hj₀⟩ := exists_chart_at hL (u.ex 0).left
  have hj₀' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U (fun _ => j₀) := by
    exact (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) (fun _ => j₀)).2 (by rw [Category.id_comp, ← h0]; exact hj₀)
  have hr₀ := valAt'_unit_ne_zero _ hj₀' (rig.s (fun _ => j₀))
  have hf₀ : u.fr j₀ 0 ≠ 0 := u.fr_ne j₀ 0 hj₀
  set r₀ := valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U (fun _ => j₀)) (rig.s (fun _ => j₀)).val with hr₀def
  let u' : HolUnif A L g :=
    { u with
      fr := fun i z => r₀ / u.fr j₀ 0 * u.fr i z
      fr_hol := fun i => (u.fr_hol i).const_mul _
      fr_ne := fun i z h => mul_ne_zero (div_ne_zero hr₀ hf₀) (u.fr_ne i z h)
      fr_compat := fun i j z h => by
        show r₀ / u.fr j₀ 0 * u.fr i z = _ * (r₀ / u.fr j₀ 0 * u.fr j z)
        rw [u.fr_compat i j z h]; ring }
  refine ⟨u', r₀ / u.fr j₀ 0, div_ne_zero hr₀ hf₀, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro j hj
  have hj1 : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U j := fun p _ => hj trivial
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U j ⊓ (L.pull (eSec A)).U (fun _ => j₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hj1, hj₀'⟩
  have hz : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U j₀) := by
    rw [top_le_preimage_inf, h0]
    exact ⟨by simpa only [Category.id_comp] using (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) j).1 hj1, by rw [← h0]; exact hj₀⟩
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr j (fun _ => j₀))
  simp only [Units.val_mul] at e
  rw [valAt'_mul] at e
  have e1 := (valAt'_res _ inf_le_left _ hm).symm.trans (e.trans (congrArg _ (valAt'_res _ inf_le_right _ hm)))
  have hg := val_pull_g L (eSec A) (𝟙 (Sp ℂ)) j (fun _ => j₀) hm
  rw [Category.id_comp] at hg
  have hc := u.fr_compat (j PUnit.unit) j₀ 0 hz
  rw [h0] at hc
  show r₀ / u.fr j₀ 0 * u.fr (j PUnit.unit) 0 = _
  rw [e1, hg, hc, ← hr₀def]
  field_simp

end GlobalTheory.RigRescale
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenericFibrePoint

theorem fibre_map_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y yF x φ hgp hL
  have hsq : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hgp.1.w, Category.assoc]; rfl
  let φ' : x.P.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift φ (x.P.A.hom ≫ yF) hsq
  have h1 : φ' ≫ Y.m.φ = φ := Y.m.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF := Y.m.cart.1.lift_snd _ _ _
  have hn : IsGrpPullback x.P.A Y.t.G (yF ≫ (Y.jQ ≫ pullback.fst _ _)) (φ' ≫ Y.m.φ) := by
    rw [h1]; exact hgp
  have hc : IsGrpPullback x.P.A Y.oF.t.G yF φ' := IsGrpPullback.cancel Y.m.cart hn h2
  refine ⟨φ', h1, h2, hc.comp Y.m0.toSABMap.cart, ?_⟩
  obtain ⟨w, hw, -⟩ := Y.m.lin
  obtain ⟨w0, hw0, -⟩ := Y.m0.toSABMap.lin
  have k : LBIso (Y.t.PP.L.pull Y.m.φ) (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) :=
    LBIso.trans (pull_isLB Y.t.PP.isLB _) Y.oF.t.PP.isLB (pull_isLB Xo.univ.t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩) ⟨w0, hw0⟩
  have k' : LBIso (Y.t.PP.L.pull φ) (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) :=
    GlobalTheory.Spread.lbIso_pull_comp φ' h1.symm rfl k
  exact LBIso.trans x.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL k'

end GlobalTheory.GenericFibrePoint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.genericFibre_group_factors_universal_cartesian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  first | exact @GlobalTheory.GenericFibrePoint.fibre_map_univ | exact GlobalTheory.GenericFibrePoint.fibre_map_univ | (intros; apply GlobalTheory.GenericFibrePoint.fibre_map_univ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultiple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

open GlobalTheory GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare

theorem exists_thetaChar_mulVec_ne {g : ℕ} (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hh : IsUnit h.det) : ∃ z, thetaChar τ c₁ c₂ (h.mulVec z) ≠ 0 := by
  have re : ∀ c : Fin g → ℂ, (∀ k, c k = 0 ∨ c k = 1 / 2) → (fun i => (((c i).re : ℝ) : ℂ)) = c := by
    intro c hc
    funext i
    rcases hc i with e | e <;> rw [e] <;> norm_num
  have hne := GlobalTheory.CanTh.thetaChar_ne_zero hs hp (fun i => (c₁ i).re) (fun i => (c₂ i).re)
  rw [re c₁ h₁, re c₂ h₂] at hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  refine ⟨h⁻¹.mulVec z₀, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  exact hz₀

theorem exists_unif_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hσ hty hP hover hgen hM
  have hh : IsUnit Θ.h.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
    ext i k
    have e := congrFun (Θ.per 0 k).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
  refine ⟨Ha.T, fun w hw yF hy₁ hy₂ hz x φ hx => ?_⟩
  have hPer := Ha.period w hw
  obtain ⟨fr, hf₁, hf₂, hf₃, -, s, hs⟩ := Θ.frame w hw
  obtain ⟨-, wx, -, hgp, hwx, -, -, -⟩ := hx
  obtain ⟨φ', hφ₁, hφ₂, hgp', hiso⟩ := GlobalTheory.T.genericFibre_group_factors_universal_cartesian E H Dw l Xo c _ _ Y yF x φ hgp ⟨wx, hwx⟩
  rw [hy₁] at hgp'
  have hL := Xo.univ.t.PP.isLB
  have hM' := LB.isLB_pull hL (φ' ≫ Y.m0.toSABMap.φ)
  let u₁ := fibreUnif hgp' (Fu.ex Ha.i (Ha.Pw w)) (Ha.Pw w).range fr (Fu.ex_add _ _ hPer) (Fu.ex_onto _ _ hPer)
    (Fu.ex_ker _ _ hPer) hPer.2.2.1 hPer.2.2.2.1 (isHolTo_exp Fu Ha.i hPer) hf₁ hf₂ hf₃
  obtain ⟨wI, hwI⟩ := LBIso.symm hiso
  let u₂ := carry u₁ hM' x.P.isLB hwI
  have hex₁ : ∀ z, (u₂.ex z).left ≫ φ' ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left := fun z =>
    liftPt_comp hgp' _
  obtain hθ : ∃ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) ≠ 0 :=
    exists_thetaChar_mulVec_ne _ _ _ _ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ hh

  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre x _ Xo.univ.t.G Xo.univ.t.PP.L (Fu.u Ha.i (Ha.Pw w)) (φ' ≫ Y.m0.toSABMap.φ) g u₂ wI
    (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr s hL hgp'.1 hwI hθ
    (fun j z hj => hf₂ j z (by rwa [hex₁] at hj))
    (fun k j z hkj => by
      obtain ⟨hk, hj⟩ := (top_le_preimage_inf _ _ _).1 hkj
      exact carry_fr u₁ hM' x.P.isLB hwI k j z hk hj)
    (fun j z p hp₁ hp₂ hj => hs j z p (hp₁.trans (hex₁ z)) hp₂ (by rwa [hex₁] at hj))
  obtain ⟨u₃, lam, hlam, hex, hΛ, hR, hfr⟩ := GlobalTheory.T.exists_rescale_uniformisation_rigidification x.P.A x.P.L g u₂ x.rig x.P.isLB x.rig_gen
  have hFn : u₃.IsFn x.th fun z => c₁ / lam * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) := by
    intro i z hi
    rw [hex] at hi ⊢
    rw [hc₁ i z hi, hfr]
    field_simp
  have hdim : g = x.P.g := by
    obtain ⟨u₀, -, -, -, -, -, hv, hw', -⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
    obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g g u₀ hv hw' u₃.ex u₃.ex_add
      (fun U f => by simpa only [Set.mem_univ, true_and] using u₃.hol U f)
    exact AHWeil.dim_eq u₃ u₀ F hF
  refine ⟨hdim.symm, u₃, c₁ / lam, hR, fun z => ⟨(u₃.ex z).left ≫ φ', ?_, ?_, ?_⟩, hΛ, hFn⟩
  · rw [Category.assoc, hex]
    exact hex₁ z
  · rw [Category.assoc, ← Category.assoc φ', hφ₂, Category.assoc, ← Category.assoc (u₃.ex z).left, Over.w (u₃.ex z),
      hy₂]
    exact Category.id_comp _
  · rw [Category.assoc, hφ₁]

end GlobalTheory.ArcNormal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultipleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  first | exact @GlobalTheory.ArcNormal.exists_unif_of_arc | exact GlobalTheory.ArcNormal.exists_unif_of_arc | (intros; apply GlobalTheory.ArcNormal.exists_unif_of_arc <;> assumption)
end
end
