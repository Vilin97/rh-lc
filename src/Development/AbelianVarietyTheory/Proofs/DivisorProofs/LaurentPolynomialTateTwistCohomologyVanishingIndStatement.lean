module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDegreeZeroBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingletonStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKilling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBase

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

noncomputable def cechDiagApp {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    yoneda.obj Y ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (by intro; exact Category.id_comp _)

theorem cechDiagApp_π {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) (j : Fin (k + 1)) :
    cechDiagApp f k ≫ WidePullback.π _ j = 𝟙 _ := WidePullback.lift_π _ _ _ _ _

theorem cechDiagApp_base {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    cechDiagApp f k ≫ WidePullback.base _ = yoneda.map f := WidePullback.lift_base _ _ _ _

noncomputable def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := cechDiagApp f n.unop.len
  naturality n m g := by
    change 𝟙 (yoneda.obj Y) ≫ cechDiagApp f m.unop.len = cechDiagApp f n.unop.len ≫ _
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      rw [cechDiagApp_π]
      erw [Category.assoc, WidePullback.lift_π]
      exact (cechDiagApp_π f _ _).symm
    · rw [cechDiagApp_base]
      refine Eq.trans ?_ (Category.assoc (cechDiagApp f _) ((cech f).map g) _).symm
      erw [WidePullback.lift_base]
      exact (cechDiagApp_base f _).symm

theorem cechDiag_spec {Y X : Scheme.{0}} (f : Y ⟶ X) :
    ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  refine ⟨cechDiag f, ?_, ?_⟩
  · refine ⟨⟨(WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 : _ ⟶ yoneda.obj Y), ?_, ?_⟩⟩
    · exact cechDiagApp_π f 0 0
    · change WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 ≫ cechDiagApp f 0 = 𝟙 _
      apply WidePullback.hom_ext
      · intro j
        rw [Fin.fin_one_eq_zero j, Category.assoc, cechDiagApp_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, cechDiagApp_base, Category.id_comp, WidePullback.π_arrow]
  · ext n : 1
    exact cechDiagApp_base f _

end GlobalTheory.EtC.GmStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBaseStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  first | (exact @GlobalTheory.EtC.GmStep.cechDiag_spec) | (exact GlobalTheory.EtC.GmStep.cechDiag_spec) | (intros; apply GlobalTheory.EtC.GmStep.cechDiag_spec  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselianStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (exact GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (intros; apply GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelZero

variable {R : Type} [CommRing R]

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem cechC_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr0 := GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap := congrArg (fun f => disc.map f) h1
  simp only [Functor.map_comp] at hmap
  have heq : ∀ x, pull _ (disc.map e.hom) (tw q i) 0 (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0 x) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0
        (pull _ (disc.map e0.hom) (tw q i) 0 x) := by
    intro x
    rw [← pull_comp, hmap, pull_comp]
    rfl
  have hcomp : (pull _ (disc.map e.hom) (tw q i) 0) ∘ (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) =
      (pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0) ∘
        (pull _ (disc.map e0.hom) (tw q i) 0) := funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e) (tw q i) 0
  have he0 : Function.Bijective (pull _ (disc.map e0.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e0) (tw q i) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr0.comp he0

end GlobalTheory.EtC.GmStep.LevelZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZeroStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (exact GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelZero.cechC_pull_bijective  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKillingStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurent_cohomology_finite_killing : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmKill.main) | (exact GlobalTheory.EtC.GmKill.main) | (intros; apply GlobalTheory.EtC.GmKill.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingIndStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) → ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gm_vanishing_step) | (exact GlobalTheory.EtC.GmStep.gm_vanishing_step) | (intros; apply GlobalTheory.EtC.GmStep.gm_vanishing_step  <;> assumption)
end
end
