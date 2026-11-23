module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
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
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber

section

@[expose] public section

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' : IsAbelianScheme A' := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ'.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ'.2 T x y (pushPt hπ'.1.w x) (pushPt hπ'.1.w y) rfl rfl,
        ← hπ'.2 T y x (pushPt hπ'.1.w y) (pushPt hπ'.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ'.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ'.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ'.1 hG.geomConnected⟩
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPoint

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem exists_sum_smul {F R : Type} [CommRing F] [CommRing R] [Algebra F R] [Algebra.Smooth F R]
    (D : Derivation ℤ R R) (hD : ∀ a, D (algebraMap F R a) = 0) (m : Ideal R) (hm : ∀ r, D r ∈ m) :
    ∃ (n : ℕ) (c : Fin n → R) (δ : Fin n → Derivation ℤ R R), (∀ k, c k ∈ m) ∧
      (∀ k a, δ k (algebraMap F R a) = 0) ∧ D = ∑ k, c k • δ k := by
  let DF : Derivation F R R :=
    { toFun := D
      map_add' := map_add D
      map_smul' := fun a r => by simp [Algebra.smul_def, hD]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  let L : Ω[R⁄F] →ₗ[R] R := DF.liftKaehlerDifferential
  have hL : ∀ r, L (KaehlerDifferential.D F R r) = D r := fun r => DF.liftKaehlerDifferential_comp_D r
  have hLm : ∀ w, L w ∈ m := by
    intro w
    have hw : w ∈ Submodule.span R (Set.range (KaehlerDifferential.D F R)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    refine (Submodule.span_le (p := Submodule.comap L m)).2 ?_ hw
    rintro _ ⟨r, rfl⟩
    show L _ ∈ m
    rw [hL]; exact hm r
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R Ω[R⁄F]
  refine ⟨n, fun k => L (p (Pi.single k 1)),
    fun k => (((LinearMap.proj k : (Fin n → R) →ₗ[R] R) ∘ₗ i).compDer (KaehlerDifferential.D F R)).restrictScalars ℤ,
    fun k => hLm _, fun k a => by simp, ?_⟩
  ext r
  have e : KaehlerDifferential.D F R r = ∑ k, i (KaehlerDifferential.D F R r) k • p (Pi.single k 1) := by
    have e0 := LinearMap.congr_fun hpi (KaehlerDifferential.D F R r)
    rw [LinearMap.comp_apply, LinearMap.id_apply, pi_eq_sum_univ' (i _)] at e0
    simpa using e0.symm
  have hs : ∀ δ : Fin n → Derivation ℤ R R, (∑ k, δ k) r = ∑ k, δ k r := fun δ => by

    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    rfl
  rw [← hL, e, hs]
  simp [mul_comm]

theorem mem_smul_top {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) [Smooth s] (I : X.IdealSheafData)
    (U : X.affineOpens) (D : logDer s I U) (m : Ideal Γ(X, U.1)) (hm : m.IsMaximal) (h : Γ(X, U.1)) (hI : h ∈ I.ideal U)
    (hh : h ∉ m) (hD : ∀ r, D.1 r ∈ m) : D ∈ m • (⊤ : Submodule Γ(X, U.1) (logDer s I U)) := by
  let φ : F →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hφ : φ.Smooth := by
    refine RingHom.Smooth.comp ?_ (Smooth.smooth_appLE s (isAffineOpen_top _) U.2 _)
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
  letI := φ.toAlgebra
  haveI : Algebra.Smooth F Γ(X, U.1) := hφ
  obtain ⟨n, c, δ, hc, hδ, e⟩ := exists_sum_smul (F := F) D.1 D.2.1 m hD
  obtain ⟨y, z, hz, hyz⟩ := hm.exists_inv hh
  let δ' : Fin n → logDer s I U := fun k => ⟨(y * h) • δ k, fun a => by
    have : δ k (constFn s U.1 a) = 0 := hδ k a
    simp [this], fun f _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hI)⟩
  have e' : D = z • D + ∑ k, c k • δ' k := by
    apply Subtype.ext
    have : (∑ k, c k • δ' k : logDer s I U).1 = (y * h) • D.1 := by
      rw [e, Finset.smul_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Submodule.coe_add, this, Submodule.coe_smul, ← add_smul, add_comm, hyz, one_smul]
  rw [e']
  exact add_mem (Submodule.smul_mem_smul hz trivial) (sum_mem fun k _ => Submodule.smul_mem_smul (hc k) trivial)

def dualConst {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

theorem constPt_spMap {K R : Type} [Field K] [CommRing R] (ψ : R →+* DualNumber K) :
    constPt (spMap ψ) = spMap (dualConst ψ) := by
  rw [constPt, spMap_comp', spMap_comp']
  rfl

theorem chart_comp {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) (U : X.affineOpens) :
    ∃ σ : F →+* Γ(X, U.1), (∀ a, σ a = constFn s U.1 a) ∧ chart U ≫ s = spMap σ := by
  refine ⟨(s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom, fun _ => rfl, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of F))) U.2 (fun _ _ => trivial)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

theorem snd_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens)
    {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (D : Γ(Y.X, U.1) → Γ(Y.X, U.1))
    (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hKS : IsKS Y.t (interior Y) U v D Θ) {K : Type} [Field K] (φ : Γ(Y.X, U.1) →+* DualNumber K)
    (hφ : ∀ r, (φ r).snd = (φ (D r)).fst) (hΘ : ∀ a b, (φ (Θ a b)).fst = 0)
    (hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y) (hc : ∀ a, (φ (constFn Y.s U.1 a)).snd = 0) (r : Γ(Y.X, U.1)) :
    (φ r).snd = 0 := by
  obtain ⟨y', hy'⟩ : ∃ y' : Sp (DualNumber K) ⟶ Xo.XF c, y' ≫ Y.j = spMap φ ≫ chart U :=
    ⟨_, IsOpenImmersion.lift_fac Y.j _ (by rintro _ ⟨p, rfl⟩; exact hV (Set.mem_univ p))⟩
  obtain ⟨σ, hσ, hcs⟩ := chart_comp Y.s U
  letI : Algebra c.F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (φ.comp σ)).toAlgebra
  obtain ⟨A', _, lam, hlam⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Y.oF.t.G y'
  obtain ⟨A₀, _, i, hi⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ' := hlam.comp Y.m0.cart
  have hι' : IsGrpPullback A' Y.t.G (spMap φ ≫ chart U) _ := (hlam.comp Y.m.cart).congr hy' rfl
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  obtain ⟨ρ, hρ, -, hiρ⟩ := exists_isConstK Y.t (interior Y) U v D Θ hv hKS φ hφ hΘ hV A₀ A' _ i hA' hι' hi
  have e₁ := eq_constPt c hi hπ' hiρ hρ
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ := by
    have h0 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h0, Category.comp_id]
  have e₂ : y' ≫ pullback.snd _ _ = spMap (φ.comp σ) := by
    rw [← hjs, reassoc_of% hy', hcs, spMap_comp']
  have e₃ : y' = constPt y' := by
    refine pullback.hom_ext e₁ ?_
    show _ = constPt (y' ≫ pullback.snd _ _)
    rw [e₂, constPt_spMap]
    congr 1
    ext a
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl, hσ, hc]
  have e₄ : spMap φ ≫ chart U = spMap (dualConst φ) ≫ chart U := by
    rw [← constPt_spMap]
    show _ = constPt (spMap φ ≫ chart U)
    rw [← hy']
    exact congrArg (· ≫ Y.j) e₃
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono (chart U) := inferInstanceAs (Mono hU.fromSpec)
  have e₅ : φ = dualConst φ := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e₄))
  rw [e₅]
  simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]



theorem mem_smul_top_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y _ hs _ _ U n v A hv _ _ D Θ m hm ⟨x, hxi, hxU, hx⟩ hKS hΘ
  have hs' := smooth_gen_iff.1 hs
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim Y.s
  have hU : IsAffineOpen U.1 := U.2
  obtain ⟨h, hle, hxh⟩ := hU.exists_basicOpen_le (V := interior Y) ⟨x, hxi⟩ hxU
  have hh : h ∉ m := fun hh => hx h hh hxh
  have hI : h ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hn
    refine hp (hle ?_)
    have : p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hn
    exact this
  refine mem_smul_top Y.s _ U D m hm h hI hh fun r => ?_
  obtain ⟨K, _, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (π : Γ(Y.X, U.1) →+* K), ∀ r, π r = 0 ↔ r ∈ m :=
    ⟨Γ(Y.X, U.1) ⧸ m, Ideal.Quotient.field m, Ideal.Quotient.mk m, fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
  obtain ⟨φ, hf, hsn⟩ : ∃ φ : Γ(Y.X, U.1) →+* DualNumber K, (∀ r, (φ r).fst = π r) ∧ ∀ r, (φ r).snd = π (D.1 r) :=
    ⟨(dualMap π).comp (epsHom D.1), fun r => by simp [epsHom, dualMap], fun r => by simp [epsHom, dualMap]⟩
  have hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y := by
    intro p _
    refine hle ?_
    have : spMap φ p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]
      intro hp
      have hu : IsUnit (φ h) := by
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf]
        exact Ne.isUnit fun h0 => hh ((hπ h).1 h0)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    exact this
  rw [← hπ, ← hsn]
  exact snd_eq_zero Y U v D.1 Θ hv hKS φ (fun r => (hsn r).trans (hf _).symm)
    (fun a b => (hf _).trans ((hπ _).2 (hΘ a b))) hV (fun a => by rw [hsn, D.2.1 a, map_zero]) r

end GlobalTheory.InteriorKS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPointStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencer_injective_closed_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.InteriorKS.mem_smul_top_of_isKS | exact GlobalTheory.InteriorKS.mem_smul_top_of_isKS | (intros; apply GlobalTheory.InteriorKS.mem_smul_top_of_isKS <;> assumption)
end
end
