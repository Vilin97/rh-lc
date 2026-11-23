module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCubeProductValueFderivAtZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.JetGeo

open ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

section Val
variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem valR_app (x : Sp A ⟶ Y) (q : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valR x (q ⁻¹ᵁ W) ((q.app W).hom f) = valR (x ≫ q) W f := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)
  · rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx
  · have hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W := hx
    unfold valR
    rw [dite_eq_right hx, dite_eq_right hx']

theorem valR_res' (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U) (e' : U ≤ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ V
  · exact GlobalTheory.ZH.CrdCalc.valR_res x e h f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun hU => h (hU.trans (x.preimage_mono e'))
    unfold valR
    rw [dite_eq_right h, dite_eq_right h']

theorem valR_pullGen (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (x : Sp A ⟶ Z) (j : K → L.ι) :
    valR x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val =
      valR (x ≫ h) (LB.wchart L φ j) (c.s j).val := by
  have e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  change valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _
  rw [valR_res' x e e']
  exact valR_app x h _ _

end Val

theorem ex_zero {B : NumB ℂ} {g : ℕ} (d : AB B g) : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ex_sum {B : NumB ℂ} {g : ℕ} (d : AB B g) {J : Type} (s : Finset J) (v : J → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem thφ_pt (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod]
  have h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i =
      ν.eA (d.ex (![x, y, z] i)) := by
    intro i; fin_cases i <;> simp [x3]
  simp_rw [h3, ← map_prod, ← ex_sum]

end Pts

theorem jet_geo : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  intro R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy
  classical

  have hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R := R) ℂ).hom := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext; simp
    simp only [TE, Over.mk_hom, redE, spMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ
  let P3 : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ G3 D.P.A) := fun z =>
    lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))
  let q : DegPre.BF D ℂ ⟶ G3 D.P.A :=
    lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))
  let h := (lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))
  have hb : ρ ≫ gm.b = ν.eA (d.ex 0) := by
    rw [ex_zero, map_one]
    ext1
    show redE ℂ ≫ gm.b.left = _
    rw [← hp.1, ho.1]
    rfl
  have hred : ρ ≫ h = P3 0 := by
    simp only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b ≫ q = h := by
    simp only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]
  have hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left := by
    intro z
    rw [ptB, ← Over.comp_left]
    congr 1
    simp only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left :=
    fun z I => thφ_pt ν d x y z I
  let j0 : thK.{0} → D.P.L.ι := fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left
  let W0 := LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0
  refine ⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩
  ·
    have hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0 := by
      funext I
      rw [Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred,
        e3]
    refine Eq.trans ?_ (valR_app _ q.left W0 _).symm
    rw [← Over.comp_left, hq]
    unfold vE DegPre.cubAtT
    refine (valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_
    rw [Category.id_comp]
    have key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val := by
      rintro _ _ rfl; rfl
    exact key _ _ hj
  · intro p _
    change (ptB ν d 0 ≫ q.left).base p ∈ W0
    rw [hpt]
    refine Set.mem_iInter.2 fun I => ?_
    have := ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)
    rw [e3] at this
    change ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)
    rw [e3]
    exact this
  · intro z hz
    refine ⟨fun I p _ => ?_, ?_⟩
    · have hm : (ptB ν d z ≫ q.left).base p ∈ W0 := hz (Set.mem_univ p)
      rw [hpt] at hm
      have := LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm
      rw [← e3 z I]
      exact this
    · change valR (ptB ν d z) _ _ = valR _ _ _
      refine (valR_app (ptB ν d z) q.left W0 _).trans ?_
      rw [hpt]

end GlobalTheory.MBLow.JetGeo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  first | exact @GlobalTheory.MBLow.JetGeo.jet_geo | exact GlobalTheory.MBLow.JetGeo.jet_geo | (intros; apply GlobalTheory.MBLow.JetGeo.jet_geo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueEqFirstJetAlternatingProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubeJet

theorem cube_jet : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  intro R _ _ D _ N g ν d G hprod W gm h0 hD χ χ' x y hx hy
  obtain ⟨U, f, hv, hU0, hUz⟩ := GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue ν d gm h0 χ χ' x y hx hy
  rw [hv, hD U f hU0]
  have hO : IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := (G.hol U f).1
  have hFeq : (fun z => valF (ptB ν d z) U f) =ᶠ[nhds 0] fun z => ∏ I : thK.{0},
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
    filter_upwards [hO.mem_nhds hU0] with z hz
    obtain ⟨hI, hval⟩ := hUz z hz
    rw [hval]
    exact hprod x y z _ hI
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := fun i => by
    have e : ∀ z, (ν.eA (d.ex z)).left = ptB ν d z ≫ (DegPre.prB D ℂ).left := fun z => by
      rw [ptB, DegPre.prB, ← Over.comp_left, lift_snd]
    have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
    simpa only [e, Scheme.Hom.comp_preimage] using this
  have hd : ∀ I : thK.{0}, DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
      (∑ i ∈ I.down, ![x, y, 0] i) := fun I =>
    (G.fr_hol _).differentiableAt ((hopen _).mem_nhds (ν.good _))
  have hn : ∀ I : thK.{0}, G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)
      (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0 := fun I => by
    rw [← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hpair : ∀ I : thK.{0}, 2 ∉ I.down →
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ (insert 2 I.down), ![x, y, 0] i))).left) =
        G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) := fun I h2 => by
    rw [Finset.sum_insert h2]
    simp
  obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero x y W (fun I : thK.{0} => G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) _
    hFeq hd hn hpair
  rw [h1, h2]
  simp [Finset.sum_insert]

end GlobalTheory.MBLow.Cl.CubeJet
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueEqFirstJetAlternatingProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cube_value_eq_first_jet_alternating_product : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  first | exact @GlobalTheory.MBLow.Cl.CubeJet.cube_jet | exact GlobalTheory.MBLow.Cl.CubeJet.cube_jet | (intros; apply GlobalTheory.MBLow.Cl.CubeJet.cube_jet <;> assumption)
end
end
