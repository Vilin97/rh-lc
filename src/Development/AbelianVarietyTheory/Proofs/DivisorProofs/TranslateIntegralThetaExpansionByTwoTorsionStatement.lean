module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisationStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAddStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_pullback_twoTorsion_translation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  first | exact @GlobalTheory.twoTors_secPull | exact GlobalTheory.twoTors_secPull | (intros; apply GlobalTheory.twoTors_secPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TwistedExpTransport



theorem expandsAt_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ a g β xe w wL ν e h hG hp h1 h2 σ σ₂ f f₂ hσ hf hE
  classical
  have hu : (U₂.gt e).pG.left ≫ (toUnit D₂.toPre.P.A).left = (thickObj R I e G).hom ≫ thick R I e := by
    have e1 := Over.w (toUnit D₂.toPre.P.A)
    have e2 := Over.w (U₂.gt e).pG
    have e3 : (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = 𝟙 _ := rfl
    rw [e3, Category.comp_id] at e1
    rw [e1, e2]
    rfl
  obtain ⟨S, hS⟩ := expandsAt_val U e 1 σ f hE
  refine expandsAt_of_val U₂ e 1 σ₂ f₂ (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  choose N hN using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U.LG.isLB (ψ y)
  have hN : Good U.LG.L y N := hN

  let ω : ((thickObj R I e G).left ⟶ D₂.toPre.P.A.left) → ((thickObj R I e G).left.presheaf.stalk y)ˣ :=
    fun ψ => gv w ψ y (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' ψ)
  have hω := fun χ => GlobalTheory.ExpTrans.prod_fam U₂ e 1 ω χ
  have hF : ∀ χ, sval (f (xe χ)) (h ≫ pGl U e) y J *
      (val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J * val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val =
      (∏ κ, ω (pGl U₂ e ≫ D₂.toPre.famφB χ κ) ^ DegPre.famε 1 κ).val * sval (f₂ χ) (pGl U₂ e) y J' := by
    intro χ
    have := hf χ _ (pGl U₂ e) y J J' hJ hJ'
    rw [hu] at this
    rw [hp]
    exact this
  have hT : ∀ χ, val ((U.gt e).t (xe χ)) h y J =
      (∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k) * val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J' *
        val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J := by
    intro χ
    have := h2 χ _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at this
    exact this
  refine ⟨fun χ hχ => ?_, fun jL' hL' => ?_⟩
  · have hi : xe χ ∉ S := fun hc => hχ (Finset.mem_map.2 ⟨xe χ, hc, xe.symm_apply_apply χ⟩)
    have z0 := (hS _ h y J hJ).1 _ hi
    have := hF χ
    rw [z0, zero_mul] at this
    exact (Units.mul_right_eq_zero _).1 this.symm
  · obtain ⟨N', hN', eN'⟩ := exists_good U₂.LG.L U₂.LG.isLB y (K := PUnit) (fun _ => fGl I G e) (fun _ => jL')
      (fun _ _ _ => rfl) (fun _ => hL')
    have eN : N' (fGl I G e) = jL' := eN' PUnit.unit
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
      have m := hN (h ≫ fGl I G e)
      have e' : N (h ≫ fGl I G e) = N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left) := congrArg N hG
      rw [e'] at m
      exact m
    have W' : ω (pGl U₂ e) * wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' =
        wv U e h y (J (h ≫ pGl U e)) (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) *
          gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL' *
          val ν ((thickObj R I e G).hom ≫ thick R I e) y J := by
      have := h1 _ (𝟙 _) y J J' N N' hJ hJ' hN hN'
      simp only [Category.id_comp] at this
      rw [hG, eN] at this
      exact this
    have Sg : sv U 1 σ (h ≫ fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) =
        (gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL').val * sv U₂ 1 σ₂ (fGl I G e) y jL' := by
      have := hσ _ (fGl I G e) y N N' hN hN'
      rw [sval_of σ _ y N (fun _ => N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun _ => by rw [Category.comp_id]),
        sval_of σ₂ _ y N' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact eN), eN] at this
      rw [hG]
      exact this
    have E := (hS _ h y J hJ).2 _ hL₁
    refine (ω (pGl U₂ e)).mul_right_inj.1 ?_
    have key : ∀ χ, (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
        (sval (f (xe χ)) (h ≫ pGl U e) y J * (val ((U.gt e).t (xe χ)) h y J).val) =
        (ω (pGl U₂ e)).val * (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) := by
      intro χ
      have hF' := hF χ
      have hω' := congrArg Units.val (hω χ)
      simp only [Units.val_mul, pow_one] at hF' hω'
      rw [hT χ]
      simp only [Units.val_mul]
      linear_combination ((∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k).val * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hF' +
        (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hω'
    have L1 : (ω (pGl U₂ e)).val * ((wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' ^ 1).val * sv U₂ 1 σ₂ (fGl I G e) y jL') =
        (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
          ∑ α ∈ S, sval (f α) (h ≫ pGl U e) y J * (val ((U.gt e).t α) h y J).val := by
      rw [← E, pow_one, pow_one, Sg, ← _root_.mul_assoc, ← Units.val_mul, W']
      simp only [Units.val_mul]
      ring
    rw [L1, Finset.sum_map, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨χ, rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe χ) = χ := xe.symm_apply_apply χ
    rw [e₀]
    exact key χ

end GlobalTheory.TwistedExpTransport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.expansion_transport_translation_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  first | exact @GlobalTheory.TwistedExpTransport.expandsAt_twist | exact GlobalTheory.TwistedExpTransport.expandsAt_twist | (intros; apply GlobalTheory.TwistedExpTransport.expandsAt_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusCoordinate_uniformisation_translate_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  first | exact @GlobalTheory.MumCmp.TranslCoord.coord_translate | exact GlobalTheory.MumCmp.TranslCoord.coord_translate | (intros; apply GlobalTheory.MumCmp.TranslCoord.coord_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.MumCmp.translate_expansion_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  obtain ⟨wL, hwL⟩ := hL
  obtain ⟨ν, hν, hW⟩ := GlobalTheory.T.exists_levelComparison_generator_of_uniformisation R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw
  obtain ⟨σ₂, hσ₂, h0⟩ := GlobalTheory.T.exists_section_pullback_twoTorsion_translation R G U.LG.L U₂.LG.L U.LG.isLB U₂.LG.isLB a ha wL hwL σ
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_translated_expansion_coefficients R D.toPre D₂.toPre β.hom hβm g xe hc w hw ν hν f
  refine ⟨σ₂, f₂, ν, hν, fun e => ?_, h0, hf₂⟩
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom ∧
      h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    ⟨pullback.lift ((fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) (thickObj R (maximalIdeal R) e G).hom
      (by rw [Category.assoc, Over.w ((toUnit G ≫ a) * 𝟙 G)]; exact pullback.condition),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  exact GlobalTheory.T.expansion_transport_translation_twist R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre a g β.hom xe w wL ν e h hh₂
    (GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβm e (hβq e)
      (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh₁ hh₂)
    (hW e h hh₁ hh₂) (GlobalTheory.T.torusCoordinate_uniformisation_translate_eq R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw xe hxe hc e h hh₁ hh₂)
    σ σ₂ f f₂ hσ₂ hf₂ (hE e)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.translate_expansion_twist | exact GlobalTheory.MumCmp.translate_expansion_twist | (intros; apply GlobalTheory.MumCmp.translate_expansion_twist <;> assumption)
end
end
