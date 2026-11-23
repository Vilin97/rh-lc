module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTriv

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidHom

theorem exists_hom_of_triv : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  intro k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hA
  let AV : GlobalTheory.AV.AbVar k := { X := A, ab := hA, dim := g, smooth := hg }
  obtain ⟨c, L, hL, hamp, -⟩ := GlobalTheory.AV.exists_isAmpleCls k AV
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp
  obtain ⟨a₁, -⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, -⟩ := hd.univ A P hP a₁
  have hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB := pull_isLB hd.isLB _
  have e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x) := (cls_eq_iff hP hE).2 hx
  refine ⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩
  apply hd.eq_one
  rw [triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]
  have u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]
  rw [u1]
  exact evc_one_right hP h₂ _

end GlobalTheory.BirigidHom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTrivStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  first | exact @GlobalTheory.BirigidHom.exists_hom_of_triv | exact GlobalTheory.BirigidHom.exists_hom_of_triv | (intros; apply GlobalTheory.BirigidHom.exists_hom_of_triv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  have pullIso : ∀ {X Y Z : Scheme.{0}} {M : LB Y} {N : LB X} {f : Y ⟶ X},
      LBIso M (N.pull f) → (g : Z ⟶ Y) → LBIso (M.pull g) (N.pull (g ≫ f)) := by
    intro X Y Z M N f H g
    exact H.chartPull (chartPullPull M g)
      (chartPullSame N (fun _ : PUnit => g ≫ f) (fun _ : PUnit => f) (fun _ => 1) g fun _ => rfl)
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), LBIso (ev P a b) (ev P₀ b (a ≫ l)) := by
    intro Y a b
    have hs := pullIso hsym (lift a b).left
    have hl' := pullIso hl (lift b a).left
    have es : LBIso (ev P a b) (ev P b a) := by
      simpa only [← Over.comp_left, comp_lift, lift_snd, lift_fst] using hs
    have el : LBIso (ev P b a) (ev P₀ b (a ≫ l)) := by
      simpa only [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc] using hl'
    exact (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).1
      (((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 es).trans
       ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 el))
  refine ⟨?_, fun T x hx => ?_⟩
  · have hs : LBIso (swap P₀) (swap P₀) := (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB hP₀ _)).1 rfl
    have hs' := pullIso hs (lift (fst A A ≫ l) (snd A A)).left
    have hs'' : LBIso (ev (swap P₀) (fst A A ≫ l) (snd A A)) (ev P₀ (snd A A) (fst A A ≫ l)) := by
      simpa only [swap, ev, ← Over.comp_left, comp_lift, lift_fst, lift_snd] using hs'
    apply (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1
    exact ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 (by simpa only [Category.comp_id] using key (A ⊗ A) (fst A A) (snd A A))).trans
      ((CechPic.cls_eq_iff (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₀ _)).2 hs'').symm
  · have hk := key (A ⊗ T) (snd A T ≫ x) (fst A T)
    simp only [Category.assoc, hx, MonObj.comp_one] at hk
    have ht : Triv (ev P₀ (fst A T) (1 : A ⊗ T ⟶ B)) := by
      obtain ⟨t, ht⟩ := hD.zero
      have h := DVR.pullGen_isGen _ _ _ t ht (fst A T).left
      simpa only [ev, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] using (show Triv _ from ⟨_, h⟩)
    exact (CechPic.iso_triv_iff _).1 ((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP _)).1
      (((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP₀ _)).2 ((CechPic.iso_triv_iff _).2 ht)).trans
        ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 hk).symm))

end GlobalTheory.AbDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (exact GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (intros; apply GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTPolPair
open GlobalTheory.AbDual

theorem nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht φ hφ x hx
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  let A' : GlobalTheory.AV.AbVar k := ⟨o₀.A, o₀.ab, g, hg⟩
  obtain ⟨B, P₀, ⟨h1, h2⟩, hdim⟩ := GlobalTheory.AV.exists_dualPair k A'
  have hgB : SmoothOfRelativeDimension g B.X.hom := by
    have := B.smooth; rw [hdim] at this; exact this
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks k o₀.A B.X o₀.ab B.ab P₀ h1 o₀.P o₀.isLB o₀.rig₁ o₀.rig₂
  obtain ⟨iso, hker⟩ := GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint k o₀.A B.X P₀ h1 o₀.P o₀.isLB o₀.symm l hlP
  obtain ⟨e, he, hkP⟩ := o₀.kerP
  have hu : IsUnit (e : k) := by
    have := (b.unit e he).map β
    simpa using this
  obtain ⟨m, hm, hlm⟩ := GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed k o₀.A B.X g o₀.ab B.ab hg hgB l hl e hu fun T y hy => hkP T y (hker T y hy)
  have hPf : IsPerfect B.X o₀.A (swap P₀) := (IsDual.isPerfect h1 h2).swap
  have CAA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  have CBA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor B.X o₀.A B.ab o₀.ab)
    (smooth_prod hgB hg)
  obtain ⟨φ', hφ'⟩ := exists_isCorrForm CBA hPf.isLB hPf.zero_left hPf.zero_right
  have hadj := IsCorrForm.adjoint CAA o₀.isLB hPf.isLB hφ hφ' l (𝟙 o₀.A) iso
  have perf := (IsCorrForm.perfect GlobalTheory.abelianDeRham B.ab hgB o₀.ab hg hPf hφ').1
  have h0 : push (dp0 k) (𝟙 _) l x = 0 := by
    refine (injective_iff_map_eq_zero _).1 perf.bijective_left.1 _ (LinearMap.ext fun y => ?_)
    rw [← hadj x y, push_id]
    exact hx y

  have hpowM : ∀ j : ℕ, IsMonHom (𝟙 o₀.A ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero]; exact isMonHom_one o₀.A o₀.A
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 o₀.A ^ n) (𝟙 o₀.A) ≫ μ[o₀.A]))
  have hpush : ∀ j : ℕ, push (dp0 k) (𝟙 _) (𝟙 o₀.A ^ j) = (j : k) • LinearMap.id := by
    intro j
    induction j with
    | zero =>
      rw [push_congr (dp0 k) (𝟙 _) (pow_zero (𝟙 o₀.A)), push_one]
      simp
    | succ n ih =>
      haveI := hpowM n
      haveI : IsMonHom (𝟙 o₀.A ^ n * 𝟙 o₀.A) := by rw [← pow_succ]; exact hpowM (n + 1)
      rw [push_congr (dp0 k) (𝟙 _) (pow_succ (𝟙 o₀.A) n), push_mul, ih, push_id]
      push_cast
      rw [add_smul, one_smul]
  haveI := hpowM e
  have key : push (dp0 k) (𝟙 _) m (push (dp0 k) (𝟙 _) l x) = (e : k) • x := by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 k) (𝟙 _) hlm, hpush]
    rfl
  rw [h0, map_zero] at key
  exact (hu.smul_eq_zero.1 key.symm)

end GlobalTheory.HTPolPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HTPolPair.nondeg | exact GlobalTheory.HTPolPair.nondeg | (intros; apply GlobalTheory.HTPolPair.nondeg <;> assumption)
end
end
