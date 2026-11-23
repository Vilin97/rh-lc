module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.RingTheory.Spectrum.Prime.RingHom
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinianStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickenings

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LocalThickGlue

theorem subsingleton_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hr := range_comap_of_surjective _ q hq
  dsimp [q] at hr
  rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero e),
    PrimeSpectrum.zeroLocus_eq_singleton] at hr
  refine ⟨fun P Q => PrimeSpectrum.comap_injective_of_surjective q hq ?_⟩
  exact Set.subsingleton_singleton (hr ▸ Set.mem_range_self P) (hr ▸ Set.mem_range_self Q)

theorem pow_succ_ne_top (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing.maximalIdeal R ^ (e + 1) ≠ ⊤ := fun h =>
  (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))

theorem exists_glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X),
    (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) →
    ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  intro R _ _ hc X x hx
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hc
  haveI hnt : ∀ e, Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top R e)
  haveI hss := subsingleton_primeSpectrum R
  let z : ∀ e, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    (Classical.arbitrary (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))))
  have hpt : ∀ e (a : Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))), x e a = x 0 (z 0) := by
    intro e
    induction e with
    | zero => intro a; rw [Subsingleton.elim (α := PrimeSpectrum _) a (z 0)]
    | succ n ih =>
      intro a
      rw [Subsingleton.elim (α := PrimeSpectrum _) a (Out.thickTrans R (IsLocalRing.maximalIdeal R) n (z n))]
      have e1 := congrArg (fun h => h (z n)) (hx n)
      simp only [Scheme.Hom.comp_apply] at e1
      rw [e1, ih]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x 0 (z 0) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : ∀ e, Set.range (x e) ⊆ Set.range hU'.fromSpec := by
    intro e
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt e a]
    exact hqU
  let ρ : ∀ e, Γ(X, U) ⟶ CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Spec.preimage (IsOpenImmersion.lift hU'.fromSpec (x e) (hr e))
  have hρ : ∀ e, Spec.map (ρ e) ≫ hU'.fromSpec = x e := fun e => by
    simp only [ρ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ e, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))).comp (ρ (e + 1)).hom =
      (ρ e).hom := fun e => by
    have h1 : ρ (e + 1) ≫ CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) =
        ρ e := by
      apply Spec.map_injective
      rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Category.assoc, hρ, hρ]
      exact hx e
    exact congrArg CommRingCat.Hom.hom h1
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  let F : Γ(X, U) →+* R := IsAdicComplete.StrictMono.liftRingHom (IsLocalRing.maximalIdeal R) ha
    (fun n => (ρ n).hom) (fun {n} => hcomp n)
  refine ⟨Spec.map (CommRingCat.ofHom F) ≫ hU'.fromSpec, fun e => ?_⟩
  have hF : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))).comp F = (ρ e).hom :=
    IsAdicComplete.StrictMono.mk_comp_liftRingHom (IsLocalRing.maximalIdeal R) ha _ _
  rw [← hρ e, ← Category.assoc]
  congr 1
  rw [Out.thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hF]
  rfl

end GlobalTheory.LocalThickGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickeningsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  first | exact @GlobalTheory.LocalThickGlue.exists_glue | exact GlobalTheory.LocalThickGlue.exists_glue | (intros; apply GlobalTheory.LocalThickGlue.exists_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdic

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFormalAssemble

theorem siegPB_id_of_tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  intro g n B _ ζ R _ _ I hI s s' c c' t ce φ ψ β hc hφ hψ hβφ hβψ
  have H := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  have hp : GlobalTheory.AbLaw.IsProjBy c.A.hom :=
    GlobalTheory.WtTower.isProjBy_of_relAmple c.A (pull_isLB c.isLB _) hc.1
  obtain ⟨G, hG, hGφ, -, -, hGP⟩ := GlobalTheory.AlgUniq.exists_iso_algebraisation H R I hI (fun e => (ce e).A) β c.A c'.A
    c.ab c'.ab hp φ ψ (fun e => (hφ e).1) hβφ (fun e => (hψ e).1) hβψ
  choose b₂ hb₂ hb₂P using fun e => (hφ e).2.1
  choose b₂' hb₂' hb₂'P using fun e => (hψ e).2.1
  have hP := hGP c.P c'.P b₂ b₂' c.isLB c'.isLB hb₂ hb₂' fun e =>
    LBIso.trans (pull_isLB c.isLB _) (ce e).isLB (pull_isLB c'.isLB _) (LBIso.symm (hb₂P e)) (hb₂'P e)
  refine ⟨G.hom.left, (G.hom ⊗ₘ G.hom).left, isGrpPullback_of_iso G, ⟨?_, ?_⟩, hP, fun a => ?_⟩
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
  · have : IsProper c'.A.hom := c'.ab.proper
    have : IsProper (𝟙_ (Over (Sp R))).hom := show IsProper (𝟙 _) from inferInstance
    have key : c.lev a ≫ G.hom = c'.lev a := by
      refine GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext H hI fun e => ?_
      have hw : pullback.fst (𝟙_ (Over (Sp R))).hom (Out.thick R I e) =
          pullback.snd (𝟙_ (Over (Sp R))).hom (Out.thick R I e) ≫ Out.thick R I e := by
        rw [← pullback.condition]; exact (Category.comp_id _).symm
      have l1 := (hφ e).2.2 a
      have l2 := (hψ e).2.2 a
      simp only [pow_one] at l1 l2
      rw [hw, Over.comp_left, Category.assoc, Category.assoc, ← reassoc_of% l1, ← l2, ← hGφ e]
    rw [Category.id_comp, ← key, Over.comp_left]

end GlobalTheory.SiegFormalAssemble
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  first | exact @GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower | exact GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower | (intros; apply GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SFamCompl

theorem glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e :=
  GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings

theorem ext_affine : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (A : Type) [CommRing A]
    (f f' : Sp R ⟶ Sp A), (∀ e, Out.thick R I e ≫ f = Out.thick R I e ≫ f') → f = f' := by
  intro R _ I hI A _ f f' h
  rw [← Spec.map_preimage f, ← Spec.map_preimage f']
  congr 1
  ext a
  refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_
  cases k with
  | zero =>
    rw [SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
    trivial
  | succ e =>
    have he := h e
    rw [← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp] at he
    have he' := congrArg (fun q => q.hom a) (Spec.map_injective he)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'
    rw [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 he'

theorem srel_comp {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
    {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · rw [pow_one, pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] (I : Ideal R) (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s) (c' : SiegPre g n (b.ζ : B) s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n (b.ζ : B) (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left), 3 ≤ n → Odd n → c.Principal → c'.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → ∃ β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left, ∀ e, β e ≫ φ (e + 1) = φ e ∧ β e ≫ ψ (e + 1) = ψ e := by
  intro g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  have key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e) :=
      GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩)
        (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)
    obtain ⟨β, hβ⟩ := (sRel_one_one_iff _ _ _).2 h1
    refine ⟨β, ?_, ?_⟩
    · have := srel_comp (hφ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)
    · have := srel_comp (hψ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)
  choose β hβ using key
  exact ⟨β, hβ⟩

theorem assemble : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) :=
  GlobalTheory.T.siegelObjects_pullback_of_compatibleTower_adic

theorem alg : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), IsAdicComplete I R → 3 ≤ n → Odd n → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s)
    (c' : SiegPre g n (b.ζ : B) s'), c.Principal → c'.Principal →
    (∀ e, ∃ (t : Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : SiegPre g n (b.ζ : B) t),
      SiegPB ce c (Out.thick R I e) ∧ SiegPB ce c' (Out.thick R I e)) → SiegPB c c' (𝟙 _) := by
  intro g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h
  choose t ce hce hce' using h
  choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)
  choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)
  obtain ⟨β, hβ⟩ := tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  exact assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)

theorem quot_local (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem quot_artin {R : Type} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m.IsMaximal)
    (N : ℕ) : IsArtinianRing (R ⧸ m ^ (N + 1)) := by
  have : Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1)) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    have hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := hp.le_of_pow_le h1
    have h3 := hm.eq_of_le hp.ne_top h2
    have h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal := h3 ▸ hm
    have h5 := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1)))
      Ideal.Quotient.mk_surjective h4
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h5
    exact h5.resolve_left hP.ne_top
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_ {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

end GlobalTheory.SFamCompl

namespace GlobalTheory.SFamCompl

theorem classified_of_complete : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ hR β c hc
  have hn0 : n ≠ 0 := by omega
  set m := IsLocalRing.maximalIdeal R with hm
  haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e
  haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e
  let βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1)) := fun e => (Ideal.Quotient.mk _).comp β
  have hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n)) := by
    intro e
    rw [spMap_id_, Category.comp_id]
    exact (spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm
  have hpull := fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)
  choose ce hce using fun e => (hpull e).1 c
  have hcep : ∀ e, (ce e).Principal := fun e => (hpull e).2.1 c (ce e) (hce e) hc
  choose x hxs hxpb using fun e => GlobalTheory.T.siegel_point_lifts_to_artinian g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)
  have hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e) :=
      GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e)
      (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)
    rw [Category.assoc, hxs (e + 1)]
    exact (spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))
  obtain ⟨f, hf⟩ := glue R hR F.X x hcomp
  have hfs : f ≫ F.s = spMap β := by
    refine ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_
    rw [← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]
  have hpf := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])
  obtain ⟨c', hc'⟩ := hpf.1 F.univ
  have hc'p : c'.Principal := hpf.2.1 F.univ c' hc' F.princ
  have key : SiegPB c c' (𝟙 _) := by
    refine alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_
    refine ⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩
    rw [hf e]
    exact hxpb e
  refine ⟨f, hfs, ?_⟩
  simpa using GlobalTheory.SiegelPullComp.pb_comp hc' key

end GlobalTheory.SFamCompl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_classifies_complete_noetherian_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SFamCompl.classified_of_complete | exact GlobalTheory.SFamCompl.classified_of_complete | (intros; apply GlobalTheory.SFamCompl.classified_of_complete <;> assumption)
end
end
