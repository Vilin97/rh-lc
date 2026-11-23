module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpen
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPartialBundleIsoNormalised
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycle
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB → ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧ (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧ (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  first | exact @GlobalTheory.LBPush.exists_push | exact GlobalTheory.LBPush.exists_push | (intros; apply GlobalTheory.LBPush.exists_push <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPartialBundleIsoNormalisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_partialBundle_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by
  first | exact @GlobalTheory.BundleNormalise.exists_iso_normalised | exact GlobalTheory.BundleNormalise.exists_iso_normalised | (intros; apply GlobalTheory.BundleNormalise.exists_iso_normalised <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  first | exact @GlobalTheory.PartialCocycle.cocycle_of_rigid | exact GlobalTheory.PartialCocycle.cocycle_of_rigid | (intros; apply GlobalTheory.PartialCocycle.cocycle_of_rigid <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedPartialLineBundles

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PartialBundleGlue

theorem iso_isGen_iff {X : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) :
    w.IsGen ↔ ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a → x ∈ M.U a' → x ∈ L.U b → x ∈ L.U b' →
      gm (𝟙 X) x (M.U a ⊓ L.U b) (w.s (a, b)) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
          gm (𝟙 X) x (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have key : ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') →
      gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ := by
    intro x a a' b b' hm
    show gm (𝟙 X) x _ (res _ (M.g a a') * (res _ (L.g b b'))⁻¹) = _
    rw [map_mul, map_inv, gm_res (𝟙 X) x _ hm, gm_res (𝟙 X) x _ hm]
  constructor
  · intro h x a a' b b' ha ha' hb hb'
    have hm : x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ha', hb'⟩
    have := congrArg (gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) (h (a, b) (a', b'))
    rw [← key x a a' b b' hm]
    exact (gm_res (𝟙 X) x _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hm _))))
  · rintro h ⟨a, b⟩ ⟨a', b'⟩
    apply unit_ext
    intro x hx
    have := h x a a' b b' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    rw [← key x a a' b b' hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

theorem pull_isGen_of {X S : Scheme.{0}} {L : LB X} {e : S ⟶ X} (r : (L.pull e).Gen)
    (h : ∀ (x : S) (a b : L.ι), e x ∈ L.U a → e x ∈ L.U b →
      gm (𝟙 S) x ((L.pull e).U fun _ => a) (r.s fun _ => a) =
        gm e x (L.U a ⊓ L.U b) (L.g a b) * gm (𝟙 S) x ((L.pull e).U fun _ => b) (r.s fun _ => b)) :
    r.IsGen := by
  intro J J'
  obtain ⟨a, rfl⟩ : ∃ a, J = fun _ => a := ⟨J PUnit.unit, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, J' = fun _ => b := ⟨J' PUnit.unit, rfl⟩
  apply unit_ext
  intro x hx
  have ha : e x ∈ L.U a := mem_pull.1 hx.1
  have hb : e x ∈ L.U b := mem_pull.1 hx.2
  have eg : gm (𝟙 S) x ((L.pull e).U (fun _ => a) ⊓ (L.pull e).U (fun _ => b))
      ((L.pull e).g (fun _ => a) (fun _ => b)) = gm e x (L.U a ⊓ L.U b) (L.g a b) := by
    show gm (𝟙 S) x _ (∏ _k : PUnit, (res _ (pullU e _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 S) x _ hx _).trans (gm_pull (𝟙 S) e x (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, eg]
  exact h x a b ha hb

theorem exists_glue : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  intro X S p e I U M hep hrig hU hM hself hr hiso
  choose r hr using hr
  choose w hw hn using fun i j => GlobalTheory.T.exists_partialBundle_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j)
    (hr i) (hr j) (hiso j i)
  have hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c →
      gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) *
        gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) =
        gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c)) := by
    intro i j k
    refine GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig
      (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_
    intro x a b c ha hb hc
    have h₁ := hn i j x a b ha hb
    have h₂ := hn j k x b c hb hc
    have h₃ := hn i k x a c ha hc
    rw [h₁, h₂, ← _root_.mul_assoc] at h₃
    exact mul_right_cancel h₃
  let L : LB X := ⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩
  · rintro ⟨i, a⟩
    apply unit_ext
    intro x hx
    rw [map_one]
    exact (gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact hc i j k x a b c hx.1.1 hx.1.2 hx.2
  · apply pull_isGen_of
    rintro x ⟨i, a⟩ ⟨j, b⟩ ha hb
    exact hn i j x a b ha hb
  · intro i
    refine ⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩
    rintro x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'
    have h₁ := hc j j' i x b b' a hb hb' ha
    have h₂ := (iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'
    rw [hself j' b' x hb', _root_.one_mul] at h₂
    rw [h₂, ← _root_.mul_assoc] at h₁
    exact h₁.symm

end GlobalTheory.PartialBundleGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedPartialLineBundlesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_glue_rigidified_partial_line_bundles : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  first | exact @GlobalTheory.PartialBundleGlue.exists_glue | exact GlobalTheory.PartialBundleGlue.exists_glue | (intros; apply GlobalTheory.PartialBundleGlue.exists_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingChartsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.generator_iso_extend_from_open_containing_charts : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  first | exact @GlobalTheory.GenPush.gen_iso_of_charts_le_range | exact GlobalTheory.GenPush.gen_iso_of_charts_le_range | (intros; apply GlobalTheory.GenPush.gen_iso_of_charts_le_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.RigidBundleGlue

variable {X Y Z : Scheme.{0}}

theorem exists_gen_of_lbIso {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem LBIso.pull {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (chartPullPull P f f rfl) (chartPullPull Q f f rfl)

def chartPullComp (L : LB X) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Z ⟶ X) (e : c = g ≫ f) :
    ChartPull (L.pull c) ((L.pull f).pull g) (𝟙 Z) := by
  subst e
  exact chartPullIn L (fun _ : PUnit => f) (fun _ => 1) g

theorem eq_one_of_section {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {e : S ⟶ A.left}
    (he : e ≫ A.hom = 𝟙 S) (V : S.Opens) (u : Γ(A.left, A.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (hu : (e.appLE _ V h).hom u = 1) : u = 1 := by
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth A.hom V
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (A.hom.app V)).2 u
  have k : ∀ (q : S ⟶ S) (_ : q = 𝟙 S) (l : V ≤ q ⁻¹ᵁ V), (q.appLE V V l).hom a = a := by
    rintro _ rfl l
    have : (𝟙 S : S ⟶ S).appLE V V l = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact S.presheaf.map_id _
    rw [this]; rfl
  have h₁ : (e.appLE _ V h).hom ((A.hom.app V).hom a) = a :=
    (congrArg (fun q => q.hom a) (Scheme.Hom.comp_appLE e A.hom V V h)).symm.trans (k (e ≫ A.hom) he h)
  rw [h₁.symm.trans hu, map_one]

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_glue : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  intro S I U A _ G _ ψ hU hψ hA _ M B a b hB hM hr hiso
  have oi : ∀ i, IsOpenImmersion (ψ i) := fun i => CoverGlue.isOpenImmersion (hψ i).1
  choose N hN₁ hN₂ hN₃ hN₄ using fun i => GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open _ _ (ψ i) (M i) (hM i)
  have hR : ∀ i x, x ∈ (ψ i).opensRange ↔ A.hom x ∈ U i := fun i x => CoverGlue.mem_range (hψ i).1 x
  have hNU : ∀ i k, (N i).U k ≤ (ψ i).opensRange := fun i k => (le_iSup (N i).U k).trans (hN₁ i).le
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨L, hL, hLr, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_partial_line_bundles A.left S A.hom e I U N he (eq_one_of_section A hA he) hU
    (fun i => (hN₁ i).trans (TopologicalSpace.Opens.ext (Set.ext (hR i)))) hN₂
    (fun i => by
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts S (U i).toScheme (U i).ι).1 _ (fun k s hs => ?_) ?_
      · have h₁ := (hR i _).1 (hNU i _ (mem_pull.1 hs))
        rw [← Scheme.Hom.comp_apply, he] at h₁
        exact ⟨⟨s, h₁⟩, rfl⟩
      · let e' : (U i).toScheme ⟶ (G i).left := eSec (G i)
        have hc : e' ≫ ψ i = (U i).ι ≫ e := eSec_comm (hψ i)
        obtain ⟨t, ht⟩ := exists_gen_of_lbIso (pull_isLB (hM i) e') (pull_isLB (hN₃ i) e')
          (LBIso.pull (hN₄ i) e') (hr i)
        obtain ⟨t', ht'⟩ := gen_chartPull (chartPullComp (N i) (ψ i) e' _ hc.symm) t ht
        exact gen_chartPull (chartPullOut (N i) (fun _ : PUnit => e) (fun _ => 1) (U i).ι _ fun _ => rfl) t' ht')
    (fun i j => by
      have : IsOpenImmersion (a i j) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hB i j).flip (oi j)
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts A.left (B i j) (a i j ≫ ψ i)).2 _ _ (fun k l x hx => ?_) ?_
      · obtain ⟨y, hy⟩ := hNU i k hx.1
        obtain ⟨y', hy'⟩ := hNU j l hx.2
        obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hB i j) y y' (hy.trans hy'.symm)
        exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
      · refine LBIso.chartPull (chartPullComp (N i) (ψ i) (a i j) _ rfl)
          (chartPullComp (N j) (ψ j) (b i j) _ (hB i j).w) ?_
        exact ((LBIso.pull (hN₄ i) (a i j)).symm.trans (pull_isLB (hN₃ i) _) (pull_isLB (hM i) _)
          (pull_isLB (hM j) _) (hiso i j)).trans (pull_isLB (hN₃ i) _) (pull_isLB (hM j) _) (pull_isLB (hN₃ j) _)
          (LBIso.pull (hN₄ j) (b i j)))
  exact ⟨L, hL, hLr, fun i => (hN₄ i).trans (hM i) (hN₃ i) (pull_isLB hL _) (LBIso.pull (hLi i) (ψ i))⟩

end GlobalTheory.RigidBundleGlue
end
end
end
