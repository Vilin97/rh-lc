module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTupleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtRelVIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRosMove

theorem rosati_alg {U : Type} [CommGroup U] (g : Fin 6 → U) (u : U) :
    (∏ k, g k ^ rosatiε k) * u * (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5) := by
  rw [Fin.prod_univ_six]
  show g 0 ^ (1 : ℤ) * g 1 ^ (-1 : ℤ) * g 2 ^ (-1 : ℤ) * g 3 ^ (-1 : ℤ) * g 4 ^ (1 : ℤ) * g 5 ^ (1 : ℤ) * u *
    (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem rosVT_move : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  intro R _ _ _ _ D D' n W T F _ _ _ N N' ν ν' O _ _ oa x ρ' hR
  obtain ⟨u, hu, u₀, hρ⟩ := hR
  have := oa.hom x
  have := oa.hom (star x)
  have hL₁ : (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).IsLB := LB.isLB_linComb D.toPre.P.isLB _ _
  obtain ⟨u'', hu'', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb D'.toPre.P.isLB _ rosatiε)
    (LB.isLB_linComb hL₁ (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε)
    (LB.linCombIso T.w _ rosatiε) (DVR.linCombIso_isGen T.w T.w_gen _ _) u hu
  refine ⟨fun a b => vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν), ⟨u'', hu'', ?_, fun _ _ => rfl⟩, ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    have h1 : (η[D'.toPre.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hz : ∀ k, (𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A).left := fun k => by
      rw [Category.id_comp, zero2, h1, ← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [MonObj.one_comp]
    choose I hI using fun χ : _ ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ y)
    have hI' : Good D'.toPre.P.L y I := hI
    have e₀ : val u (𝟙 _ ≫ zero2 D'.toPre.P.A) y I = 1 := by
      have := val_corr hI' u₀ (𝟙 _)
      rwa [val_pull hI', val_one] at this
    have m₁ := hJ.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have m₂ := hI'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have H := hv _ (𝟙 _ ≫ zero2 D'.toPre.P.A) y _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (𝟙 _ ≫ zero2 D'.toPre.P.A) y ⟨m₁, m₂⟩
    refine H.trans (Eq.trans (congrArg₂ (· * ·) G e₀) ?_)
    rw [_root_.mul_one]
    have key : ∀ Fn : (_ ⟶ D'.toPre.P.A.left) → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left.presheaf.stalk y)ˣ,
        ∏ a, Fn ((𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) a) ^ rosatiε a = 1 := by
      intro Fn
      simp only [hz]
      simp [Fin.prod_univ_succ, rosatiε]
    exact key (fun ψ => gm ψ y (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (J ψ, I ψ))
      (T.w.s (J ψ, I ψ)))
  · intro a b
    let z : Sp F := IsLocalRing.closedPoint F
    have hN : Good D.toPre.P.L z ν.J := fun q => ν.good q trivial
    have hJ' : Good D'.toPre.P.L z ν'.J := fun q => ν'.good q trivial
    have mT : ∀ y : Sp F ⟶ D'.toPre.P.A.left,
        y z ∈ (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).U (GlobalTheory.Mum.TensRos.tensJ T ν y) :=
      fun y => Set.mem_iInter.2 fun k => hN (y ≫ tensφ T.pr k)
    have m₁ : (lift (ν'.eA a) (ν'.eA b)).left z ∈ LB.wchart (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W))
        (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x))
        (fun k => GlobalTheory.Mum.TensRos.tensJ T ν ((lift (ν'.eA a) (ν'.eA b)).left ≫
          rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k)) := Set.mem_iInter.2 fun k => mT _
    have m₂ := hJ'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (lift (ν'.eA a) (ν'.eA b)).left
    have H := hv _ (lift (ν'.eA a) (ν'.eA b)).left z _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (lift (ν'.eA a) (ν'.eA b)).left z ⟨m₁, m₂⟩
    let Gp : N'.A → ((Sp F).presheaf.stalk z)ˣ := fun p => gm (ν'.eA p).left z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
        (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
    have hW : ∀ p, toStk z (wv T ν ν' p) = (Gp p).val := fun p => by
      have hm : (ν'.eA p).left z ∈ (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
          (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left)) := ⟨mT _, hJ' _⟩
      exact toStk_valF _ _ z hm _
    have ea : ∀ y c, ν'.eA (GlobalTheory.Relabel.actV ν' oa y c) = ν'.eA c ≫ oa.act y := fun y c => ν'.eA.apply_symm_apply _
    let pts : Fin 6 → N'.A := ![GlobalTheory.Relabel.actV ν' oa (star x) a * b, GlobalTheory.Relabel.actV ν' oa (star x) a, b,
      a * GlobalTheory.Relabel.actV ν' oa x b, a, GlobalTheory.Relabel.actV ν' oa x b]
    have hp : ∀ k, (lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (ν'.eA (pts k)).left := fun k => by
      rw [← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [pts, ea]
    have key : ∀ Fn : (Sp F ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ,
        ∏ k, Fn ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k) ^ rosatiε k =
          ∏ k, Fn (ν'.eA (pts k)).left ^ rosatiε k := fun Fn => by simp only [hp]
    have G' := G.trans (key (fun ψ => gm ψ z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))))
    have v'' := toStk_valF _ _ z m₁ (u''.s _)
    have v' : toStk z (ρ' a b) = (gm (lift (ν'.eA a) (ν'.eA b)).left z _ (u.s fun k => ν'.J
        ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k))).val := by
      rw [hρ]; exact toStk_valF _ _ z m₂ _
    have HH := H.trans (congrArg₂ (· * ·) G' rfl)
    apply (toStk z).injective
    show toStk z (vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν) * _) = _
    simp only [map_mul, hW, v']
    erw [v'', HH]
    simp only [← Units.val_mul]
    congr 1
    exact rosati_alg (fun k => Gp (pts k)) _

end GlobalTheory.Mum.TensRosMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  first | exact @GlobalTheory.Mum.TensRosMove.rosVT_move | exact GlobalTheory.Mum.TensRosMove.rosVT_move | (intros; apply GlobalTheory.Mum.TensRosMove.rosVT_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensRos

theorem main_alg {F : Type} [Field F] (a1 a2 P1 P2 s1 s2 A Bv C Dd E' G one : F) (hA : A ≠ 0) (hB : Bv ≠ 0)
    (hE : E' ≠ 0) (hG : G ≠ 0) (hD : Dd ≠ 0)
    (h1 : a2 * (A * Bv * C) = a1 * (Dd * E' * G)) (h2 : a2 * P1 = P2) (h3 : s1 * A * Bv = P1 * Dd * one)
    (h4 : s2 * E' * G = P2 * C * one) : s2 = s1 * a1 := by
  have hK : A * Bv * E' * G * Dd ≠ 0 := by positivity
  apply mul_right_cancel₀ hK
  linear_combination (A*Bv*Dd)*h4 - (a1*E'*G*Dd)*h3 - (A*Bv*Dd*C*one)*h2 + (P1*one*Dd)*h1

theorem rosGt_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ' hρ' v' w' vs hv hw
  letI := H.starRing
  obtain ⟨ρ'', hT, hmove⟩ := GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle R hB D D' W T F N N' ν ν' (𝓞 E) o.onB x ρ' hρ'
  obtain ⟨-, hbij, -, -, -, hwv0, -, -⟩ := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  rw [GtRel, gtRelV_iff] at hv hw
  intro χ
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x v'.b := by
    apply hbij.1
    funext j
    rw [hw.1 j, cmp_actV T ν ν' o ρ hact x v'.b j, ← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, NumD.projB_apply, hv.1 k]
  have h1 := hmove (N'.c χ) v'.b
  rw [c_actV ν' o] at h1
  have h2 := GlobalTheory.T.rosatiGenerator_components_torusExtension R hB D D' W T F N N' ν ν' E H ρ hρ o hact x ρ'' hT χ v'.b vs hv.1
  have h3 := hv.2 (ν'.eX.symm (star x • ν'.eX χ))
  have h4 := hw.2 χ
  rw [hb] at h4
  exact main_alg _ _ _ _ _ _ _ _ _ _ _ _ _ (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) h1 h2 h3 h4

end GlobalTheory.Mum.TensRos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.rosati_values_tensor_data_matrix_action : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  first | exact @GlobalTheory.Mum.TensRos.rosGt_values | exact GlobalTheory.Mum.TensRos.rosGt_values | (intros; apply GlobalTheory.Mum.TensRos.rosGt_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensAct

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) [Module O D'.X]
    (o : D'.OAct O) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (i : Fin r) :
    TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) i = ∏ j, TensTor.cmp T ν ν' b j ^ ρ x i j := by
  letI := D.P.isAb.comm
  simp only [TensTor.cmp, GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x i]
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := by simp [Hom.one_def]
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have := map_prod (ν.eA.symm.toMonoidHom.comp P) (fun j => T.pr j ^ ρ x i j) Finset.univ
  simp only [map_zpow] at this
  exact this

end GlobalTheory.Mum.TensAct
namespace GlobalTheory.Mum.TensAct

section V
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem rel_one (hF : TensFacts W φ e wv) : GtRelV W φ e wv 1 1 := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W φ e wv hF 1
  have h2 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF u u 1 1 hu hu
  rw [_root_.mul_one] at h2
  have h3 : u * u = u := GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hF _ _ _ h2 hu
  rw [_root_.mul_eq_left] at h3
  exact h3 ▸ hu

theorem rel_pow (hF : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) :
    ∀ m : ℕ, GtRelV W φ e wv (v' ^ m) (vs ^ m)
  | 0 => by simpa using rel_one hF
  | m + 1 => by
    rw [_root_.pow_succ, _root_.pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF _ _ _ _ (rel_pow hF h m) h

end V

theorem io_sum {O : Type} [CommRing O] (N : NumD O) {κ : Type} (s : Finset κ) (m : κ → ℤ) (y : κ → N.X) :
    N.io (∑ j ∈ s, m j • y j) = ∏ j ∈ s, N.io (y j) ^ m j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, N.io_add, ih]
    congr 1
    have := N.ioHom.map_zpow (Multiplicative.ofAdd (y k)) (m k)
    simpa [NumD.ioHom, ← ofAdd_zsmul] using this

def qTH {O : Type} [CommRing O] (N : NumD O) (k : ℕ) : Multiplicative N.X →* N.QT k :=
  MonoidHom.mk' (fun z => N.qTriv k z.toAdd) fun a b => Subtype.ext (Prod.ext
    (by simp [NumD.qTriv, smul_add, ofAdd_add]) (by simp [NumD.qTriv, N.io_add]))

theorem qEq_iff_mk {O : Type} [CommRing O] (N : NumD O) {k : ℕ} (p p' : N.QT k) :
    N.QEq p p' ↔ (p : N.QT k ⧸ (qTH N k).range) = p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [qTH]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    have : N.qTriv k z.toAdd = p⁻¹ * p' := hz
    rw [this, mul_inv_cancel_left]

end GlobalTheory.Mum.TensAct

open GlobalTheory.Mum.TensAct in
theorem GlobalTheory.Mum.TensAct.qkAct_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact g ev hadd hker n hn x a p' q' hp hq
  letI := H.starRing
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have hB := GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have hB' := GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  beta_reduce at hB hB'
  obtain ⟨q0, qs, hq0, hqs, hrel0⟩ := hp
  obtain ⟨q1, qs1, hq1, hqs1, hrel1⟩ := hq
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).1 o.onB x
  let us : Fin r → N.QT n := fun i => ∏ j, qs j ^ ρ x i j
  let ts : Fin r → N.Gt := fun i => ∏ j, (qs j).1.2 ^ ρ x i j
  have hts : ∀ i, (us i).1.2 = ts i := fun i => by
    show ((MonoidHom.snd _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j) = ∏ j, (qs j).1.2 ^ ρ x i j
    rw [map_prod]
    simp only [map_zpow]
    rfl
  have husy : ∀ i, (us i).1.1.toAdd = ∑ j, ρ x i j • (qs j).1.1.toAdd := fun i => by
    show Multiplicative.toAdd (((MonoidHom.fst _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j)) = _
    rw [map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow]
    rfl
  obtain ⟨w', hw'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W _ _ _ hF ts
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x q0.1.2.b := by
    apply hF.2.1.1
    funext i
    rw [cmp_actV T ν ν' ρ o hact x _ i, hw'.1 i]
    simp only [ts]
    rw [← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, NumD.projB_apply, hrel0.2.1 j]
  have hros := GlobalTheory.T.rosati_values_tensor_data_matrix_action R hR D D' W T F N N' ν ν' E H ρ hρ o hact x ρ' hρ' q0.1.2 w' (fun j => (qs j).1.2) hrel0.2 hw'

  set y'' : N'.X := ν'.eX.symm (x • p'.y) with hy''
  have hey : ∀ i, TensTor.chi T ν ν' y'' i = (us i).1.1.toAdd := fun i => by
    rw [husy i]
    have h1 : ν'.eX y'' = x • p'.y := by rw [hy'', AddEquiv.apply_symm_apply]

    simp only [TensTor.chi, h1, hact.1 x p'.y i, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hrel0.1 j, ← hq0.1]
    rfl
  have hwn : w' ^ n = N'.io y'' := by
    have hpow := rel_pow hF hw' n
    have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF y''
    have e1 : ts ^ n = fun j => N.io (TensTor.chi T ν ν' y'' j) := funext fun i => by
      rw [hey i, husy i, io_sum]
      simp only [Pi.pow_apply, ts, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← (qs j).2]
      rw [← zpow_natCast, ← zpow_natCast ((qs j).1.2), ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e1] at hpow
    exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hpow hio
  let tv : N'.QT n := ⟨(Multiplicative.ofAdd y'', w'), by rw [NumD.mem_QT]; exact hwn⟩
  obtain ⟨t', ht'⟩ := (hB'.2.2.2.2 n).2.1 tv

  have hex : ∀ b, ∃ c, ν.QPt (ev n b) c := fun b => ((hB.2.2.2.2 n).1 (ev n b)).exists
  choose qv hqv using hex
  have huniq : ∀ b c, ν.QPt (ev n b) c → c = qv b := fun b c h =>
    ((hB.2.2.2.2 n).1 (ev n b)).unique h (hqv b)
  have haddv : ∀ b c, N.QEq (qv b * qv c) (qv (b + c)) := fun b c => by
    obtain ⟨q, hqy, hqadd, hqeq⟩ := hadd n hn b c
    obtain ⟨cq, hcq⟩ := ((hB.2.2.2.2 n).1 q).exists
    have e1 : cq = qv b * qv c := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        change ν.eX cq.1.1.toAdd = ν.eX ((qv b).1.1.toAdd + (qv c).1.1.toAdd)
        rw [map_add (f := _), (hqv b).1, (hqv c).1, hcq.1, hqy]
      · exact (hB.2.2.1 _ _ _ _ _ _ (hqv b).2 (hqv c).2 hcq.2).1 hqadd
    rw [← e1]
    exact ((hB.2.2.2.2 n).2.2 q (ev n (b + c)) cq (qv (b + c)) hcq (hqv _)).1 hqeq
  let f : Multiplicative ((Fin g → ℤ) × (Fin g → ℤ)) →* N.QT n ⧸ (qTH N n).range :=
    MonoidHom.mk' (fun b => ((qv b.toAdd : N.QT n) : N.QT n ⧸ (qTH N n).range)) fun b c => by
      rw [toAdd_mul, ← (qEq_iff_mk N _ _).1 (haddv _ _), QuotientGroup.mk_mul]
  have hQi : ∀ i, N.QEq (us i) (qs1 i) := fun i => by
    rw [qEq_iff_mk, huniq _ _ (hqs1 i)]
    have h1 : ((qv (∑ j, ρ x i j • a j) : N.QT n) : N.QT n ⧸ (qTH N n).range) =
        f (Multiplicative.ofAdd (∑ j, ρ x i j • a j)) := rfl
    rw [h1, ofAdd_sum, map_prod]
    simp only [us, QuotientGroup.mk_prod, QuotientGroup.mk_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ofAdd_zsmul, map_zpow, huniq _ _ (hqs j)]
    rfl
  choose z hz1 hz2 using hQi
  obtain ⟨z', hz'⟩ := hF.2.2.2.1.2 z
  let eH : N'.X →+ (Fin r → N.X) := AddMonoidHom.mk' (TensTor.chi T ν ν') fun a b => funext (hF.2.2.1 a b)
  have hQ : N'.QEq tv q1 := by
    refine ⟨z', ?_, ?_⟩
    · apply hF.2.2.2.1.1
      have hs : TensTor.chi T ν ν' (y'' + n • z') = TensTor.chi T ν ν' y'' + n • TensTor.chi T ν ν' z' :=
        (map_add eH _ _).trans (congrArg _ (map_nsmul eH n z'))
      change TensTor.chi T ν ν' q1.1.1.toAdd = TensTor.chi T ν ν' (y'' + n • z')
      rw [hs]
      funext i
      rw [Pi.add_apply, Pi.smul_apply]
      rw [hrel1.1 i, hz1 i, hey i, hz']
    · have hm := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W _ _ _ hF _ _ _ _ hw' (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF z')
      have e2 : ts * (fun j => N.io (TensTor.chi T ν ν' z' j)) = fun j => (qs1 j).1.2 := funext fun i => by
        rw [Pi.mul_apply, hz2 i, hts i, hz']
      rw [e2] at hm
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hrel1.2 hm
  refine ⟨t', ?_, ?_, ((hB'.2.2.2.2 n).2.2 t' q' tv q1 ht' hq1).2 hQ⟩
  · rw [← ht'.1]
    exact AddEquiv.apply_symm_apply _ _
  · exact ((GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).2 o x ρ' hρ' p'.g t'.g q0.1.2 w'
      hq0.2 ht'.2).2 ⟨hb, hros⟩
end
end
end
