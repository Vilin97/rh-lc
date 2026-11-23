module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVeryAmplePowerStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfSmoothThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRingStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomOfThickeningsStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_compatible_sections_thickenings_localRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  first | exact @GlobalTheory.SecLifts.exists_compatible_sections_local | exact GlobalTheory.SecLifts.exists_compatible_sections_local | (intros; apply GlobalTheory.SecLifts.exists_compatible_sections_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfThickenings

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgLocal

open GlobalTheory.MorAlg GlobalTheory.LBAlg

theorem exists_veryAmpleBy_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')} {φ : X' ⟶ X} (g : R →+* R')
    (h : IsPullback φ f' f (Spec.map (CommRingCat.ofHom g))) {H : LB X} (hH : H.IsLB) {m : ℕ}
    {σ : Fin (m + 1) → LB.Sec H} (hσ : VeryAmpleBy f H σ) :
    ∃ σ' : Fin (m + 1) → LB.Sec (H.pull φ), VeryAmpleBy f' (H.pull φ) σ' := by
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull φ hH σ
  refine ⟨σ₀, GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H m σ hH hσ _ g _ _ φ h.w ?_ _ w₀ _
    (pull_isLB hH _) hw₀ c₀⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [e]
  infer_instance

theorem exists_lineBundle_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ I hI hcomp Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  choose σ' hva using fun e =>
    exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk (I ^ (e + 1))) (hb e) hH hσ
  have hI' : I ^ (0 + 1) ≠ ⊤ := by simpa using hI
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (R ⧸ I ^ (0 + 1))
  let _ := Ideal.Quotient.field 𝔪
  have hπ := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪)))
  generalize pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = f₀ at hπ
  generalize pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = π at hπ
  obtain ⟨σ₀, hσ₀⟩ := exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk 𝔪) hπ (hL 0) (hva 0)
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (pull_isLB (hL 0) π) hσ₀ ((N 0).pull π) (pull_isLB (hN 0).1 π)
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) (hva 0) (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl)
        (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  have hP : ∀ e, IsProjBy (Y e).hom := fun e => ⟨_, hL e, m, σ' e, hva e⟩
  obtain ⟨w₀, hw₀⟩ : LBIso (tw ((N 0).pull π) ((H.pull (b 0)).pull π) t) ((tw (N 0) (H.pull (b 0)) t).pull π) :=
    LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) t)
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT 0))
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hflY hP
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) _ (Ideal.Quotient.mk 𝔪)
    Ideal.Quotient.mk_surjective _ π f₀ hπ _ w₀ (isLB_tw (pull_isLB (hN 0).1 π) (pull_isLB (hL 0) π) t) hw₀
    (ht₁ t h₁) (u j)
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.GenSystem.exists_lb_of_generated_system R I hI hcomp Y β hβ B b hB hfl hb hc
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) n (fun e j => s j e) (fun e j => hs j e)
    (by simpa only [hs0] using hu)
  have hM' : (tw M H (-t)).IsLB := isLB_tw hM hH _
  refine ⟨tw M H (-t), hM', fun e => ?_⟩
  have hO' : (tw (M.pull (b e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hM _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM' _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) (hNM e)))
    (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM'))

end GlobalTheory.LBAlgLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLocaStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formal_complete_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  first | exact @GlobalTheory.Degen.exists_projective_of_formal_embedding_local | exact GlobalTheory.Degen.exists_projective_of_formal_embedding_local | (intros; apply GlobalTheory.Degen.exists_projective_of_formal_embedding_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickeningStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_lift_squareZero_thickening : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  first | exact @GlobalTheory.AmpleThickening.relAmple_of_sq_zero | exact GlobalTheory.AmpleThickening.relAmple_of_sq_zero | (intros; apply GlobalTheory.AmpleThickening.relAmple_of_sq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBaseStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  first | exact @GlobalTheory.AmpleLocalBase.relAmple_of_closed | exact GlobalTheory.AmpleLocalBase.relAmple_of_closed | (intros; apply GlobalTheory.AmpleLocalBase.relAmple_of_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompatibleLineBundlesFormalThickening

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalAlgebraise

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = ⊥ := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)


open GlobalTheory.AbLaw in
theorem algebraisation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro _ _ R _ _ _ _ I hI hc _ Y β N v hβ hY hN hA
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hfl : ∀ e, Flat (Y e).hom := fun e => by have := hY e; infer_instance
  have hamp : ∀ e, RelAmple (Y e) (N e) := by
    intro e
    induction e with
    | zero => exact hA
    | succ e ih =>
      have := hY (e + 1)
      exact GlobalTheory.T.relAmple_lift_squareZero_thickening _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) (Y (e + 1)) (Y e) (β e)
        (hβ e) inferInstance _ _ (hN _).1 (hN _).1 ⟨v e, (hN e).2⟩ ih
  have hproj : ∀ e, AbLaw.IsProjBy (Y e).hom := fun e => by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ (Y e) (N e) (hN e).1).1 (hamp e)
    exact ⟨_, isLB_pw (hN e).1 _, n, s, hs⟩
  have hle : I ^ (0 + 1) ≤ IsLocalRing.maximalIdeal R := by
    rw [zero_add, pow_one]
    exact IsLocalRing.le_maximalIdeal hI
  let g₀ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.factor hle
  have hg₀ : Function.Surjective g₀ := Ideal.Quotient.factor_surjective hle
  have hpb := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := GlobalTheory.T.exists_very_ample_power _ (Y 0) (N 0) (hN 0).1 hA _ g₀ _ _ _ hpb
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [GlobalTheory.Algebraise.pw_pull]
    exact GlobalTheory.Algebraise.lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  have hL := LB.isLB_pull (hN' 0).1 (pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)))
  choose s hs using fun j => GlobalTheory.T.exists_compatible_sections_thickenings_localRing R I hI Y β hβ hfl hproj
    (fun e => AbLaw.pw (N e) d) v' hN' _ g₀ hg₀ _ _ _ hpb _ _ hL (CubePf.idIsoL_isGen hL) h0 (s₀ j)
  have hva : AbLaw.VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext (fun j => (hs j).1)
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, -, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formal_complete_local R I hI hc Y β hβ hfl
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => (hs j).2 e) hva
  have hP : AbLaw.IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have hS : Smooth B.hom := GlobalTheory.T.smooth_of_smooth_thickenings' R I hI B (AbLaw.isProper_of_isProjBy R B.left B.hom hP) Y b hb hY
  have hF : Flat B.hom := inferInstance
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlgLocal.exists_lineBundle_of_thickenings R I hI hc Y β hβ B b hP hF hb hbβ N v hN
  haveI : Nontrivial (R ⧸ I ^ (0 + 1)) := g₀.domain_nontrivial
  exact ⟨B, M, b, hP, hS, hM, GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase R B M hF hP hM _ _ Ideal.Quotient.mk_surjective (Y 0) (b 0) (hb 0)
    (N 0) (hN 0).1 (hNM 0) hA, hb, hbβ, hNM⟩

end GlobalTheory.FormalAlgebraise
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompatibleLineBundlesFormalThickeningStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.compatible_line_bundles_formal_thickening : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  first | exact @GlobalTheory.FormalAlgebraise.algebraisation | exact GlobalTheory.FormalAlgebraise.algebraisation | (intros; apply GlobalTheory.FormalAlgebraise.algebraisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.ega_of_laws : Laws → Laws2 → Ega := fun h₁ h₂ =>
  ⟨GlobalTheory.T.compatible_line_bundles_formal_thickening h₁ h₂, GlobalTheory.T.existsUnique_hom_of_thickenings' h₁ h₂, GlobalTheory.SecAlg.existsUnique_sec, GlobalTheory.T.exists_section_primitiveBundle_translate_localRing h₁ h₂⟩
end
end
