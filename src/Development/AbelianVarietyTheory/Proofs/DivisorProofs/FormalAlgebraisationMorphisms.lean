module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfProperIsIsoOnReductionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.ExtremalEpi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTower

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTowerStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.formal_algebraisation_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  first | exact @GlobalTheory.FormalAlg.alg_tower | exact GlobalTheory.FormalAlg.alg_tower | (intros; apply GlobalTheory.FormalAlg.alg_tower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparatedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.grothendieck_existence_closedSubschemes_separated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isSeparated | exact GlobalTheory.FormalAlg.alg_of_isSeparated | (intros; apply GlobalTheory.FormalAlg.alg_of_isSeparated <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem hom_eq_of_reductions_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hb g g' hg
  have hι : IsClosedImmersion (equalizer.ι g g').left := isClosedImmersion_equalizer_ι_left g g'
  have hN : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hle : ∀ e : ℕ, (equalizer.ι g g').left.ker ≤ baseIdeal X.hom (I ^ (e + 1)) := by
    intro e
    rw [← (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X.left (Y e).left X.hom (b e) (Y e).hom (hb e)).2.1]
    let c : Over.mk (b e ≫ X.hom) ⟶ X := Over.homMk (b e) rfl
    have hc : c ≫ g = c ≫ g' := by
      ext
      exact hg e
    have h1 : (equalizer.lift c hc).left ≫ (equalizer.ι g g').left = b e := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : (equalizer.ι g g').left.ker ≤ ⊥ :=
    GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X.left X.hom _ ⊥ inferInstance fun e => (hle e).trans le_sup_right
  have hiso : IsIso (equalizer.ι g g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.2 (le_bot_iff.1 hbot)
  ext
  rw [← cancel_epi (equalizer.ι g g').left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickeningsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.morphism_eq_of_eq_on_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | exact GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | (intros; apply GlobalTheory.FormalAlg.hom_eq_of_reductions_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlgMorphisms

variable {R : Type} [CommRing R]

instance isClosedImmersion_thick (I : Ideal R) (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem isPullback_trans {I : Ideal R} (X : Over (Spec (CommRingCat.of R)))
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left)
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (e : ℕ) : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := by
  have hw : β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, ← (hb (e + 1)).w, ← Category.assoc,
      hβ, (hb e).w, Category.assoc, thickTrans_comp]
  refine IsPullback.of_right ?_ hw (hb (e + 1))
  rw [hβ, thickTrans_comp]
  exact hb e

theorem formalAlgebraisation_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    haveI := hI
    exact IsAdicComplete.le_jacobson_bot I

  let fW : pullback X.hom Z.hom ⟶ Spec (CommRingCat.of R) := pullback.fst X.hom Z.hom ≫ X.hom
  haveI : IsSeparated (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback X.hom Z.hom).flip hZs
  haveI : LocallyOfFiniteType (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback X.hom Z.hom).flip hZl
  haveI : QuasiCompact (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback X.hom Z.hom).flip hZq
  have hAlg : Alg fW I := GlobalTheory.T.grothendieck_existence_closedSubschemes_separated R I hI _ fW inferInstance inferInstance inferInstance

  have hcomm : ∀ e, b e ≫ X.hom = f e ≫ Z.hom := fun e => by rw [(hb e).w, hf e]
  let j : ∀ e, (Y e).left ⟶ pullback X.hom Z.hom := fun e => pullback.lift (b e) (f e) (hcomm e)
  have hj₁ : ∀ e, j e ≫ pullback.fst X.hom Z.hom = b e := fun e => pullback.lift_fst _ _ _
  have hj₂ : ∀ e, j e ≫ pullback.snd X.hom Z.hom = f e := fun e => pullback.lift_snd _ _ _
  have hbci : ∀ e, IsClosedImmersion (b e) := fun e =>
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb e).flip inferInstance
  have hjci : ∀ e, IsClosedImmersion (j e) := fun e => by
    haveI : IsClosedImmersion (j e ≫ pullback.fst X.hom Z.hom) := by rw [hj₁]; exact hbci e
    exact IsClosedImmersion.of_comp (j e) (pullback.fst X.hom Z.hom)
  have hjf : ∀ e, j e ≫ fW = (Y e).hom ≫ thick R I e := fun e => by
    simp only [fW]
    rw [← Category.assoc, hj₁, (hb e).w]
  have hjβ : ∀ e, β e ≫ j (e + 1) = j e := fun e => by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hj₁, hβ]
    · rw [Category.assoc, hj₂, hj₂, hfβ]
  have hYp : ∀ e, IsProper (Y e).hom := fun e =>
    MorphismProperty.of_isPullback (P := @IsProper) (hb e) hX
  obtain ⟨T, i, c, hi, hip, hci, hcpb⟩ := GlobalTheory.T.formal_algebraisation_tower R I _ fW hAlg Y β
    (isPullback_trans X Y β b hb hβ) hYp j hjci hjf hjβ

  let φ : T ⟶ X.left := i ≫ pullback.fst X.hom Z.hom
  have hφX : φ ≫ X.hom = i ≫ fW := Category.assoc _ _ _
  haveI : IsProper (φ ≫ X.hom) := by rw [hφX]; exact hip
  haveI : IsProper φ := IsProper.of_comp φ X.hom
  have hcφ : ∀ e, c e ≫ φ = b e := fun e => by
    simp only [φ]
    rw [← Category.assoc, hci, hj₁]
  haveI hφiso : IsIso φ := GlobalTheory.T.isIso_of_proper_isIso_on_reductions R I hIj T X.left φ X.hom inferInstance hX Y c
    (fun e => by rw [hφX]; exact hcpb e) (fun e => by rw [hcφ]; exact hb e)

  let gl : X.left ⟶ Z.left := inv φ ≫ i ≫ pullback.snd X.hom Z.hom
  have hgw : gl ≫ Z.hom = X.hom := by
    simp only [gl, Category.assoc]
    rw [← pullback.condition, ← Category.assoc i, ← Category.assoc (inv φ)]
    exact IsIso.inv_hom_id_assoc φ X.hom
  refine ⟨Over.homMk gl hgw, fun e => ?_, fun g' hg' => ?_⟩
  · show b e ≫ gl = f e
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]
  · refine GlobalTheory.T.morphism_eq_of_eq_on_thickenings R I hIj X Z hX hZs Y b hb g' _ fun e => ?_
    rw [hg' e]
    show f e = b e ≫ gl
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]

end GlobalTheory.FormalAlgMorphisms
end
end
end
