module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PGrpFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPlaceOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPtAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels


theorem UpperTheory.Gal.FiniteEtaleModels.crtMul_holds :
    CrtMul := by
  intro p _ D R _ b N S s o 𝔞 𝔟 hab T l₁ l₂ h1 h2
  have hmon : ∀ c, IsMonHom (o.act.act c) := o.act.hom
  obtain ⟨a, ha, b', hb, habe⟩ : ∃ a ∈ 𝔞, ∃ b' ∈ 𝔟, a + b' = 1 := by
    have h1m : (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 := by
      rw [hab]
      exact Submodule.mem_top
    obtain ⟨a, ha, b', hb, h⟩ := Submodule.mem_sup.1 h1m
    exact ⟨a, ha, b', hb, h⟩
  have split : ∀ {X : Over S} (f : X ⟶ o.A),
      f ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) * f ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = f := by
    intro X f
    rw [← MonObj.comp_mul, ← o.act.add, ← map_add (f := _), habe, map_one, o.act.one, Category.comp_id]
  have gen : ∀ (I : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y : D.La,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D I 1 := by
    intro I c hc y
    exact Submodule.subset_span ⟨c, by simpa using hc, y, rfl⟩
  have mulsub : ∀ (I J : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y ∈ wSub D J 1,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D (I * J) 1 := by
    intro I J c hc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c', hc', z', rfl⟩ := hz
      rw [← mul_smul, ← map_mul]
      exact gen _ _ (Ideal.mul_mem_mul hc (by simpa using hc')) z'
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul o' x _ hx =>
      rw [← mul_smul, Algebra.commutes, mul_smul]
      exact Submodule.smul_mem _ _ hx
  have wmono : ∀ (I J : Ideal (𝓞 D.F)), I ≤ J → wSub D I 1 ≤ wSub D J 1 := by
    intro I J h
    apply Submodule.span_mono
    rintro z ⟨c, hc, z', rfl⟩
    exact ⟨c, by simpa using h (by simpa using hc), z', rfl⟩
  have kill : ∀ (I : Ideal (𝓞 D.F)) (l : D.La → (T ⟶ o.A)), IsEtLevOver o I 1 l →
      ∀ {X : Over S} (P : X ⟶ T) (y : D.La) (c : 𝓞 D.F), c ∈ I →
        (P ≫ l y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro I l hl X P y c hc
    rw [Category.assoc, ← hl.2.1, hl.2.2.1 _ (gen I c hc y), MonObj.comp_one]
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · dsimp only
    rw [h1.1, h2.1]
    exact mul_mul_mul_comm _ _ _ _
  · dsimp only
    rw [h1.2.1, h2.2.1, MonObj.mul_comp]
  · dsimp only
    have hxa : x ∈ wSub D 𝔞 1 := wmono (𝔞 * 𝔟) 𝔞 (Ideal.mul_le_left : 𝔞 * 𝔟 ≤ 𝔞) hx
    have hxb : x ∈ wSub D 𝔟 1 := wmono (𝔞 * 𝔟) 𝔟 (Ideal.mul_le_right : 𝔞 * 𝔟 ≤ 𝔟) hx
    rw [h1.2.2.1 x hxa, h2.2.2.1 x hxb]
    exact mul_one 1
  · dsimp only at hy
    rw [MonObj.comp_mul] at hy
    have hu : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y = 1 := by
      have e1 := congrArg (· ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) hy
      simp only [MonObj.mul_comp, MonObj.one_comp, kill _ l₂ h2 _ _ _ hb, _root_.mul_one] at e1
      rw [← split (Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y), kill _ l₁ h1 _ _ _ ha, e1, _root_.one_mul]
    have hv : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₂ y = 1 := by
      rw [hu, _root_.one_mul] at hy
      exact hy
    have y1 := (h1.2.2.2 k x).1 y hu
    have y2 := (h2.2.2.2 k x).1 y hv
    have hsplit : y = algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b' • y := by
      rw [← add_smul, ← map_add (f := _), habe, map_one, one_smul]
    rw [hsplit]
    refine Submodule.add_mem _ (mulsub 𝔞 𝔟 a ha y y2) ?_
    have h3 := mulsub 𝔟 𝔞 b' hb y y1
    rwa [mul_comm] at h3
  · have hg' : ∀ c ∈ 𝔞 * 𝔟, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hg c (by simpa using hc)
    have hk1 : ∀ c ∈ 𝔞, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul]
      exact hg' _ (Ideal.mul_mem_mul hc hb)
    have hk2 : ∀ c ∈ 𝔟, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm]
      exact hg' _ (Ideal.mul_mem_mul ha hc)
    obtain ⟨y₁, hy₁⟩ := (h1.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))
      (fun c hc => hk1 c (by simpa using hc))
    obtain ⟨y₂, hy₂⟩ := (h2.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
      (fun c hc => hk2 c (by simpa using hc))
    have e1 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))]
      rw [hk1 a ha, _root_.one_mul]
    have e2 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))]
      rw [hk2 b' hb, _root_.mul_one]
    refine ⟨algebraMap (𝓞 D.F) D.O b' • y₁ + algebraMap (𝓞 D.F) D.O a • y₂, ?_⟩
    dsimp only
    rw [h1.1, h2.1, h1.2.2.1 _ (gen 𝔞 a ha y₂), h2.2.2.1 _ (gen 𝔟 b' hb y₁), _root_.mul_one, _root_.one_mul,
      h1.2.1, h2.2.1, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hy₁, hy₂, e1, e2, mul_comm]
    exact split g
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.finModel_holds :
    FinCover → FinModel := by
  intro cover p _ D R _ _ b N h3 hcop 𝔞 r h𝔞 M
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, q, u, mu, lev, act, hlev, hgal, hrep⟩ :=
    cover p D R b N 𝔞 r h3 hcop h𝔞 M.X M.s M.univ
  let E : EtModel b N 𝔞 r :=
    { X := Y, s := q ≫ M.s, univ := u, lv := lev, isLev := hlev
      rep := by
        intro T t o l hl
        obtain ⟨c, ⟨hc, ⟨mc⟩⟩, cuniq⟩ := M.rep T t o
        subst hc
        obtain ⟨f, ⟨hfq, m₂, hm₂⟩, funiq⟩ := hrep T c o mc l hl
        refine ⟨f, ⟨?_, m₂, hm₂⟩, ?_⟩
        · rw [← Category.assoc, hfq]
        · rintro f' ⟨hs, m', hm'⟩
          refine funiq f' ⟨?_, m', hm'⟩
          obtain ⟨mcomp⟩ := objMap_comp p D R b N T Y M.X (c ≫ M.s) (q ≫ M.s) M.s o u M.univ f' q m' mu
          exact cuniq (f' ≫ q) ⟨by rw [Category.assoc, ← hs], ⟨mcomp⟩⟩ }
  exact ⟨E, q, act, rfl, ⟨mu⟩, hgal⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PIdealInd

section

@[expose] public section

namespace UpperTheory.Gal.FiniteEtaleModels

theorem idealInd_holds : IdealInd := by
  intro A _ _ Q P htop hpow hmul 𝔞
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h => absurd rfl h
  | h1 hx =>
    rename_i x
    intro _ _
    rw [Ideal.isUnit_iff.1 hx]
    exact htop
  | hpr i hp =>
    rename_i w
    intro _ hQ
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact htop
    · have hmax : w.IsMaximal :=
        (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
      exact hpow w i hmax (hQ w hmax (Ideal.pow_le_self hi.ne'))
  | hcp hxy hx hy =>
    rename_i x y
    intro hne hQ
    have hx0 : x ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.bot_mul y)
    have hy0 : y ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.mul_bot x)
    have hsup : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact hmul x y hsup
      (hx hx0 fun w hw hle => hQ w hw (Ideal.mul_le_left.trans hle))
      (hy hy0 fun w hw hle => hQ w hw (Ideal.mul_le_right.trans hle))

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.repMul_holds :
    CrtMul → CrtProj → RepMul := by
  intro hM hP p _ D R _ b N S s o 𝔞 𝔟 hab h₁ h₂
  obtain ⟨Y₁, π₁, lu₁, hf₁, he₁, hl₁, hu₁⟩ := h₁
  obtain ⟨Y₂, π₂, lu₂, hf₂, he₂, hl₂, hu₂⟩ := h₂
  haveI := hf₁
  haveI := hf₂
  haveI := he₁
  haveI := he₂
  obtain ⟨ea, hea, eb, heb, hsum⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 by rw [hab]; exact Submodule.mem_top)
  have kill : ∀ {𝔠 : Ideal (𝓞 D.F)} {T : Over S} {l : D.La → (T ⟶ o.A)}, IsEtLevOver o 𝔠 1 l →
      ∀ e ∈ 𝔠, ∀ y, l (algebraMap (𝓞 D.F) D.O e • y) = 1 := fun h e he y =>
    h.2.2.1 _ (Submodule.subset_span ⟨e, by simpa using he, y, rfl⟩)
  have dec : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ea • y + algebraMap (𝓞 D.F) D.O eb • y = y := by
    intro y
    rw [← add_smul, ← map_add (f := _), hsum, map_one, one_smul]
  have r₁ : ∀ y, lu₁ (algebraMap (𝓞 D.F) D.O eb • y) = lu₁ y := by
    intro y
    conv_rhs => rw [← dec y, hl₁.1, kill hl₁ ea hea, _root_.one_mul]
  have r₂ : ∀ y, lu₂ (algebraMap (𝓞 D.F) D.O ea • y) = lu₂ y := by
    intro y
    conv_rhs => rw [← dec y, hl₂.1, kill hl₂ eb heb, _root_.mul_one]
  let π : pullback π₁ π₂ ⟶ S := pullback.fst π₁ π₂ ≫ π₁
  let f₁ : Over.mk π ⟶ Over.mk π₁ := Over.homMk (pullback.fst π₁ π₂) rfl
  let f₂ : Over.mk π ⟶ Over.mk π₂ := Over.homMk (pullback.snd π₁ π₂) pullback.condition.symm
  refine ⟨pullback π₁ π₂, π, fun y => (f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y), inferInstance, inferInstance, ?_, ?_⟩
  · exact hM p D R b N S s o 𝔞 𝔟 hab _ _ _ (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 1 _ _ lu₁ f₁ hl₁)
      (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔟 1 _ _ lu₂ f₂ hl₂)
  · intro T l hl
    have hA := hP p D R b N S s o 𝔞 𝔟 eb heb (by rw [← hsum, add_sub_cancel_right]; exact hea) T l hl
    have hB := hP p D R b N S s o 𝔟 𝔞 ea hea (by rw [← hsum, add_sub_cancel_left]; exact heb) T l
      (by rwa [_root_.mul_comm])
    obtain ⟨g₁, hg₁, hv₁⟩ := hu₁ T _ hA
    obtain ⟨g₂, hg₂, hv₂⟩ := hu₂ T _ hB
    have hg₁' : ∀ y, g₁ ≫ lu₁ y = l (algebraMap (𝓞 D.F) D.O eb • y) := hg₁
    have hg₂' : ∀ y, g₂ ≫ lu₂ y = l (algebraMap (𝓞 D.F) D.O ea • y) := hg₂
    have hw : g₁.left ≫ π₁ = g₂.left ≫ π₂ := (Over.w g₁).trans (Over.w g₂).symm
    let f : T ⟶ Over.mk π := Over.homMk (pullback.lift g₁.left g₂.left hw) (by
      show pullback.lift g₁.left g₂.left hw ≫ pullback.fst π₁ π₂ ≫ π₁ = T.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w g₁)
    have c₁ : f ≫ f₁ = g₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ hw)
    have c₂ : f ≫ f₂ = g₂ := Over.OverMorphism.ext (pullback.lift_snd _ _ hw)
    refine ⟨f, ?_, ?_⟩
    · intro y
      show f ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, c₁, c₂, hg₁', hg₂', ← hl.1,
        add_comm, dec]
    · intro f' hf'
      have hf'' : ∀ y, f' ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y := hf'
      have a₁ : f' ≫ f₁ = g₁ := hv₁ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O eb • y)
        rw [kill hl₂ eb heb, r₁, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
          ← Category.assoc] at this
        exact this)
      have a₂ : f' ≫ f₂ = g₂ := hv₂ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O ea • y)
        rw [kill hl₁ ea hea, r₂, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.one_mul,
          ← Category.assoc] at this
        exact this)
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · have := congrArg (fun u => u.left) (a₁.trans c₁.symm)
        simpa [f₁] using this
      · have := congrArg (fun u => u.left) (a₂.trans c₂.symm)
        simpa [f₂] using this
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovLink

section

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.CovMain

open UpperTheory.Gal.FiniteEtaleModels in
theorem mIn : MIn :=
  { ex := @GlobalTheory.T.harrisTaylorIntegralModel_nonempty,
    proj := @GlobalTheory.UPel.HT.Model.isProjOver_of_compactB,
    cmp := @GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre,
    finModel := finModel_holds (finCover_holds
      (repAll_holds idealInd_holds (repMul_holds crtMul_holds crtProj_holds))
      (ptAll_holds idealInd_holds crtMul_holds) grpFin_holds),
    placeOf := placeOf_holds,
    cong := crystallineComparison.Mod.congKS_link,
    corr := crystallineComparison.Mod.corrBC_holds crystallineComparison.Mod.quotObj_link }

theorem ksCong_holds : KSCong := kSCong_of mIn
theorem stdEx_holds : StdEx := stdEx_of mIn
theorem ksCover_holds : KSCover := kSCover_of mIn

end UpperTheory.Gal.Int.Geo.CovMain
end
end
