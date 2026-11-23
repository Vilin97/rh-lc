module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsClassifyMarkedPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfComplexBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexBaseChangePolarizedAbelianFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_isBC : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g),
    ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  intro O _ g R _ σ Λ F
  let f : pullback F.s (spMap σ) ⟶ F.X := pullback.fst _ _
  let A' : Over (pullback F.s (spMap σ)) := (Over.pullback f).obj F.A
  letI : GrpObj A' := Functor.grpObjObj
  have hP : IsGrpPullback A' F.A f (pullback.fst F.A.hom f) := isGrpPullback_pullback F.A f
  haveI : IsCommMonObj A' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hP
  obtain ⟨act', ⟨hh, h1, hm, ha⟩, hc⟩ := GlobalTheory.ActPull.exists_act_pull _ _ f F.A A' _ hP Oᵐᵒᵖ
    (fun a => F.act a.unop) (fun a => F.hom _) F.act_one (fun a b => F.act_mul b.unop a.unop)
    (fun a b => F.act_add _ _)
  have hLB := LB.isLB_pull F.isLB (pullback.fst F.A.hom f)
  have hpol := GlobalTheory.pol_pull _ _ F.A A' f _ F.L (F.L.pull _) F.isLB hLB F.ab hP (GlobalTheory.PolBaseChange.lbIso_refl hLB)
  have hdim : SmoothOfRelativeDimension g A'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hP.1 F.dim
  let eta' : Λ → (𝟙_ (Over (pullback F.s (spMap σ))) ⟶ A') := fun a =>
    Over.homMk (hP.1.lift (f ≫ (F.eta a).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; simp)) (hP.1.lift_snd _ _ _)
  refine ⟨Fam.mk (pullback F.s (spMap σ)) (pullback.snd _ _) A' hpol.1 hdim (fun a => act' (MulOpposite.op a))
    (fun a => hh _) h1 (fun a b => by rw [MulOpposite.op_mul]; exact hm _ _)
    (fun a b => by rw [MulOpposite.op_add]; exact ha _ _)
    (F.L.pull (pullback.fst F.A.hom f)) hLB (hpol.2.1 F.ample) eta',
    f, pullback.fst F.A.hom f, IsPullback.of_hasPullback _ _, hP, fun a => hc _,
    GlobalTheory.PolBaseChange.lbIso_refl hLB, fun a => hP.1.lift_fst _ _ _⟩

end GlobalTheory.PELU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexBaseChangePolarizedAbelianFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_complexBaseChange_polarizedAbelianFamily : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g), ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  first | exact @GlobalTheory.PELU.exists_isBC | exact GlobalTheory.PELU.exists_isBC | (intros; apply GlobalTheory.PELU.exists_isBC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem spMap_id_complex : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
  simp [spMap]

theorem fineAt_of_isBC (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type)
    [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop)
    (F' : Fam ℂ O Λ g) (hBC : IsBC F' F σ) (hF : FineAt F σ ρ N C) : FineAt F' (RingHom.id ℂ) ρ N C := by
  obtain ⟨f, φ, pb, gp, hact, hL, heta⟩ := hBC
  have M := GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ gp hact hL heta
  have base : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' hy
    rw [Category.assoc, pb.w, ← Category.assoc, hy, spMap_id_complex, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro y' hy
    obtain ⟨D', t, P, e, hC, hU⟩ := hF.pts (y' ≫ f) (base y' hy)
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy (base y' hy)).2 e hU
    exact ⟨D', t, P, e', hC, hU'⟩
  · intro D' t P hC hP
    obtain ⟨y, e, hU⟩ := hF.occ D' t P hC hP
    have w : y ≫ F.s = spMap (RingHom.id ℂ) ≫ spMap σ := by
      rw [hU.1, spMap_id_complex, Category.id_comp]
    obtain ⟨y', rfl, hy'⟩ : ∃ y', y' ≫ f = y ∧ y' ≫ F'.s = spMap (RingHom.id ℂ) :=
      ⟨pb.lift y _ w, pb.lift_fst _ _ w, pb.lift_snd _ _ w⟩
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy' (base y' hy')).2 e hU
    exact ⟨y', e', hU'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w h hw hP
    obtain ⟨e₁, hU₁, -⟩ := (M D' t P y hU.1 (base y hU.1)).1 e hU
    obtain ⟨e₂, hU₂, -⟩ := (M D'' t' P' y' hU'.1 (base y' hU'.1)).1 e' hU'
    have hf : y ≫ f = y' ≫ f := hF.sep D' D'' t t' P P' _ _ e₁ e₂ hU₁ hU₂ w h hw hP
    exact pb.hom_ext hf (hU.1.trans hU'.1.symm)

end GlobalTheory.PELU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g), IsBC F' F σ → FineAt F σ ρ N C → FineAt F' (RingHom.id ℂ) ρ N C := by
  first | exact @GlobalTheory.PELU.fineAt_of_isBC | exact GlobalTheory.PELU.fineAt_of_isBC | (intros; apply GlobalTheory.PELU.fineAt_of_isBC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfIsGrpPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem pow_eq_one_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (hG : IsGrpPullback G' G f φ) (e : 𝟙_ (Over S) ⟶ G)
    (e' : 𝟙_ (Over S') ⟶ G') (h : e'.left ≫ φ = f ≫ e.left) (N : ℕ) (hN : e ^ N = 1) : e' ^ N = 1 := by
  let T : Over S' := 𝟙_ (Over S')
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]; rfl)
  have hψ : ∀ x y, ψ (x * y) = ψ x * ψ y := fun x y => by
    ext1
    exact (hG.2 T x y (ψ x) (ψ y) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' ψ hψ
  have inj : Function.Injective ψ := fun x y hxy => by
    ext1
    apply hG.1.hom_ext
    · exact congrArg CommaMorphism.left hxy
    · rw [Over.w x, Over.w y]
  have h1 : ψ e' = toUnit _ ≫ e := by
    ext1
    simp only [ψ, Over.homMk_left, Over.comp_left, h]
    congr 1
  apply inj
  have : Ψ (e' ^ N) = Ψ 1 := by
    rw [map_pow, map_one]
    show (ψ e') ^ N = 1
    rw [h1, ← comp_pow, hN, comp_one]
  exact this

end GlobalTheory.PELU

namespace GlobalTheory.PELU

theorem nonempty_unif : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) → FineAt F σ ρ N C → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C d hN heta hsm hqc hfull hfine
  obtain ⟨F', hbc⟩ := GlobalTheory.T.exists_complexBaseChange_polarizedAbelianFamily O g R σ Λ F
  obtain ⟨f, φ, hX, hA, -, -, heta'⟩ := id hbc
  have e' : ∀ a, F'.eta a ^ N = 1 := fun a =>
    pow_eq_one_of_isGrpPullback f φ hA (F.eta a) (F'.eta a) (heta' a) N (heta a)
  have s' : SmoothOfRelativeDimension d F'.s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback hX hsm
  have q' : QuasiCompact F'.s := MorphismProperty.of_isPullback hX hqc
  exact GlobalTheory.T.complexUniformisation_of_complexBaseChange O bar g ρ R σ Λ F N C F' hbc
    (GlobalTheory.T.complexUniformisation_of_markedPeriods_family O bar g ρ Λ F' N C d hN e' s' q' hfull (GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange O bar g ρ R σ Λ F N C F' hbc hfine))

end GlobalTheory.PELU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem quasiCompact_of_qProj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f := by
  obtain ⟨N, i, -, hi, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem Obj.eta_pow {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (x : D.La) : o.eta x ^ N = 1 := by
  have h0 : o.eta 0 = 1 := by
    have h := o.eta_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hn : ∀ n : ℕ, o.eta (n • x) = o.eta x ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
  rw [← hn, o.eta_ker]

theorem Datum.Cls.fullMark {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hp : N.Coprime p)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (h : D.Cls N D' t) : FullMark N D' t := by
  obtain ⟨⟨f, ν, rfl, -, hf⟩, -⟩ := h
  exact (hf N hN hp).2.2.2.1

theorem model_uniformised : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N), 3 ≤ N → N.Coprime p →
    b.IsType σ ρ → M.Uniformised σ ρ := by
  intro p _ D R _ b N σ ρ M hN hp hty
  obtain ⟨h, hL⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N M.X M.s M.univ
  refine ⟨h, hL, ?_⟩
  exact GlobalTheory.PELU.nonempty_unif D.O D.inv D.g ρ R σ D.La (M.univ.fam h hL) N (D.Cls N) (D.a * (D.n - 1)) hN
    (fun a => M.univ.eta_pow a) M.smooth (quasiCompact_of_qProj M.qproj)
    (fun D' t hc => Datum.Cls.fullMark D N (by omega) hp D' t hc)
    (GlobalTheory.T.complexPoints_classify_markedPeriods p D R b N σ ρ M h hL (by omega) hp hty)

end GlobalTheory.UPel.HT
end
end
end
