module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.AlgebraicGeometry.QuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionCover

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

namespace GlobalTheory.GlueOver

open GlobalTheory.KS

variable {X : Scheme.{0}}

theorem rsT_cocycle {M : LB X} (hM : M.IsLB) (a b c : M.ι) {O : X.Opens} (h : O ≤ M.U a ⊓ M.U b ⊓ M.U c) :
    rsT (M.g a b).val O * rsT (M.g b c).val O = rsT (M.g a c).val O := by
  have e := congrArg (fun u => rsT u.val O) (hM.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, rsT_mul] at e
  rwa [rsT_rsT inf_le_left h, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem rsT_g_self {M : LB X} (hM : M.IsLB) (a : M.ι) {O : X.Opens} (h : O ≤ M.U a) :
    rsT (M.g a a).val O = 1 := by
  have h2 : O ≤ M.U a ⊓ M.U a := le_inf h h
  have e := rsT_cocycle hM a a a (le_inf h2 h)
  have hu : IsUnit (rsT (M.g a a).val O) := by
    rw [rsT_of_le h2]
    exact (M.g a a).isUnit.map _
  exact hu.mul_left_cancel (e.trans (_root_.mul_one _).symm)

theorem exists_glue : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens)
    (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) →
    (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) →
    ∃ t : ∀ c, Γ(X, M.U c ⊓ V),
      (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) =
        rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧
      ∀ i, rsT (t (j i)) (W i) = F i := by
  intro X M hM V J W j F hV hW Fc
  have hWV : ∀ i, W i ≤ V := fun i => hV ▸ le_iSup W i
  have cov : ∀ O : X.Opens, O ⊓ V ≤ ⨆ i, O ⊓ W i := by
    intro O y hy
    have : y ∈ ⨆ i, W i := by rw [hV]; exact hy.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy.1, hi⟩
  have hU : ∀ c i, M.U c ⊓ W i ≤ M.U c ⊓ M.U (j i) := fun c i => inf_le_inf le_rfl (hW i)
  have hUV : ∀ (O : X.Opens) i, O ⊓ W i ≤ O ⊓ V := fun O i => inf_le_inf le_rfl (hWV i)
  have glue : ∀ c : M.ι, ∃ t : Γ(X, M.U c ⊓ V), ∀ i,
      rsT t (M.U c ⊓ W i) = rsT (M.g c (j i)).val (M.U c ⊓ W i) * rsT (F i) (M.U c ⊓ W i) := by
    intro c
    refine exists_rsT_eq (fun i => M.U c ⊓ W i) (fun i => hUV _ i) (cov _) _ fun i i' => ?_
    have hN1 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i := inf_le_left
    have hN2 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i' := inf_le_right
    have hNW : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ W i ⊓ W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have h3 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ M.U (j i) ⊓ M.U (j i') :=
      fun y hy => ⟨⟨hy.1.1, hW i hy.1.2⟩, hW i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_rsT (hU c i) hN1, rsT_rsT (hU c i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_rsT (inf_le_inf (hW i) (hW i')) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  choose t ht using glue
  refine ⟨t, fun c c' => ?_, fun i => ?_⟩
  · refine eq_of_rsT_eq (fun i => M.U c ⊓ M.U c' ⊓ W i) (fun i => hUV _ i) (cov _) _ _ fun i => ?_
    have a1 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c' ⊓ W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have h3 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ M.U (j i) := inf_le_inf le_rfl (hW i)
    have e' : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ V := hUV _ i
    have eL : M.U c ⊓ M.U c' ⊓ V ≤ M.U c ⊓ V := fun y hy => ⟨hy.1.1, hy.2⟩
    have eR : M.U c ⊓ M.U c' ⊓ V ≤ M.U c' ⊓ V := fun y hy => ⟨hy.1.2, hy.2⟩
    rw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', rsT_rsT inf_le_left e',
      ← rsT_rsT (hUV _ i) a1 (t c), ← rsT_rsT (hUV _ i) a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_rsT (hU c i) a1, rsT_rsT (hU c' i) a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  · have a : W i ≤ M.U (j i) ⊓ W i := le_inf (hW i) le_rfl
    rw [← rsT_rsT (hUV _ i) a, ht, rsT_mul, rsT_rsT (hU _ i) a, rsT_rsT inf_le_right a, rsT_self,
      rsT_g_self hM (j i) (hW i), _root_.one_mul]

end GlobalTheory.GlueOver
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionCoverStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_cover : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens) (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) → (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) → ∃ t : ∀ c, Γ(X, M.U c ⊓ V), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧ ∀ i, rsT (t (j i)) (W i) = F i := by
  first | exact @GlobalTheory.GlueOver.exists_glue | exact GlobalTheory.GlueOver.exists_glue | (intros; apply GlobalTheory.GlueOver.exists_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpen

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecAff

theorem rsT_eq_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) : rsT s V = rs h s :=
  GlobalTheory.KS.rsT_of_le h s

theorem sec_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  intro X _ _ M hM f t ht
  let φ := (X.basicOpen f).ι
  have hφ : φ.opensRange = X.basicOpen f := Scheme.Opens.opensRange_ι _
  have hr : ∀ x, φ x ∈ X.basicOpen f := by
    intro x
    have hx : φ x ∈ φ.opensRange := ⟨x, rfl⟩
    rwa [hφ] at hx
  have hc : ∀ c, φ ⁻¹ᵁ M.U c ≤ φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) := fun c x hx => ⟨hx, hr x⟩
  let t' : ∀ c, Γ(↑(X.basicOpen f), φ ⁻¹ᵁ M.U c) := fun c => pa φ (hc c) (t c)
  have ht' : ∀ i j, rs (inf_le_left : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U i) (t' i) =
      pa φ (le_pre_inf (inf_le_left.trans (le_refl (φ ⁻¹ᵁ M.U i)))
        (inf_le_right.trans (le_refl (φ ⁻¹ᵁ M.U j))))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U j) (t' j) := by
    intro i j
    have e : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ (M.U i ⊓ M.U j ⊓ X.basicOpen f) :=
      fun x hx => ⟨⟨hx.1, hx.2⟩, hr x⟩
    have h1 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have h2 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ M.U j := inf_le_left
    have h3 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U j ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    have := ht i j
    rw [rsT_eq_rs h1, rsT_eq_rs h2, rsT_eq_rs h3] at this
    have := congrArg (pa φ e) this
    rw [map_mul, pa_rs, pa_rs, pa_rs] at this
    simp only [t']
    rw [rs_pa, rs_pa]
    exact this
  obtain ⟨N, s, hs⟩ := sec_extend φ f hφ M hM (fun c => φ ⁻¹ᵁ M.U c) (fun c => le_rfl)
    (fun c => le_rfl) t' ht'
  refine ⟨N, s, fun c => ?_⟩
  have hU : M.U c ⊓ X.basicOpen f ≤ φ.opensRange := by rw [hφ]; exact inf_le_right
  apply (pa_bijective φ (le_refl (φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f))) le_rfl hU).1
  have hV : φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) ≤ φ ⁻¹ᵁ M.U c := fun x hx => hx.1
  have := congrArg (rs hV) (hs c)
  rw [rs_pa, map_mul, map_pow, rs_pa] at this
  simp only [t'] at this
  rw [rs_pa] at this
  rw [rsT_eq_rs inf_le_left, rsT_eq_rs le_top, map_mul, map_pow, pa_rs, pa_rs, this]

end GlobalTheory.SecAff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpenStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

theorem _root_.GlobalTheory.T.exists_lineBundleSection_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  first | exact @GlobalTheory.SecAff.sec_extend_basicOpen | exact GlobalTheory.SecAff.sec_extend_basicOpen | (intros; apply GlobalTheory.SecAff.sec_extend_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstant

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVExt
open GlobalTheory.KS

theorem cst_resV {Y : Scheme.{0}} {R : Type} [CommRing R] (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1) (r : R) :
    GlobalTheory.HeatV.cst π _ h (GlobalTheory.HeatV.resV R c r) = rsT (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) O := by
  rw [rsT_of_le le_top]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.map_appLE π (U := (GlobalTheory.HeatV.bo R c).1) (U' := ⊤) (V := O) h (homOfLE le_top).op)

theorem rsT_cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (a : Γ(X, V)) : rsT (GlobalTheory.HeatV.cst π V h a) O' = GlobalTheory.HeatV.cst π V (h'.trans h) a := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_natCast {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Y, O₀)) O = m := by
  rw [rsT_of_le h, map_natCast]

theorem rsT_two {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (2 : Γ(Y, O₀)) O = 2 := by
  rw [rsT_of_le h, map_ofNat]

theorem opV_rsT : ∀ {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → GlobalTheory.Heat.Fld Y), (∀ a, IsField ⊤ (dd a)) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)) (u : Fin n → Γ(X, V)) (d : GlobalTheory.Heat.Fld Y) {W : Y.Opens}, IsField W d → ∀ (p p' : Γ(Y, W)) (k : ℕ) {O O' : Y.Opens} (hOW : O ≤ W) (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O) (f : Γ(Y, O)), rsT (GlobalTheory.HeatV.opV π V dd Θ u d p p' k O h f) O' = GlobalTheory.HeatV.opV π V dd Θ u d p p' k O' (h'.trans h) (rsT f O') := by
  intro Y X π V n dd hdd Θ u d W hd p p' k O O' hOW h h' f
  have hd' : ∀ g, resG Y h' (d O g) = d O' (resG Y h' g) :=
    fun g => ((hd.2.2 O O' h' hOW g)).symm
  have hdd' : ∀ a g, resG Y h' (dd a O g) = dd a O' (resG Y h' g) :=
    fun a g => ((hdd a).2.2 O O' h' le_top g).symm
  have hc : ∀ r, resG Y h' (GlobalTheory.HeatV.cst π V h r) = GlobalTheory.HeatV.cst π V (h'.trans h) r :=
    fun r => (rsT_of_le h' _).symm.trans (rsT_cst π V h h' r)
  have hp : ∀ q : Γ(Y, W), resG Y h' (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h', rsT_rsT hOW h']
  rw [rsT_of_le h', rsT_of_le h']

  simp only [GlobalTheory.HeatV.opV, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem heat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n dd' hdd' D Θ₁ DV hDV J W j d u pf pf' hW hcov hWL hd hdc hglue k σ a
  set π := t.G.hom
  set M := LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)) with hMdef
  have hM : M.IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  set f : Γ(t.G.left, ⊤) := π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) with hfdef
  have hb : π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 = t.G.left.basicOpen f := Scheme.preimage_basicOpen_top π _
  have hWc : ∀ i, W i ≤ M.U (fun _ => j i) := fun i => GlobalTheory.Heat.Glue.le_wchart _ (hWL i)
  let F : ∀ i, Γ(t.G.left, W i) := fun i =>
    GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c a) *
                 GlobalTheory.HeatV.opV π _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) -
      2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) *
        rsT (σ.f fun _ => j i) (W i)
  have hF : ∀ i i', rsT (F i) (W i ⊓ W i') =
      rsT (M.g (fun _ => j i) (fun _ => j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i') := by
    intro i i'
    have hII : W i ⊓ W i' ≤ M.U (fun _ => j i) ⊓ M.U (fun _ => j i') := inf_le_inf (hWc i) (hWc i')
    have hs := GlobalTheory.Heat.Glue.sec_rel (𝟙 t.G.left) k σ (fun _ => j i) (fun _ => j i') hII
    have hgl := hglue k i i' (W i ⊓ W i') le_rfl (rsT (σ.f fun _ => j i') (W i ⊓ W i'))
    rw [GlobalTheory.Heat.Glue.linComb_g (𝟙 t.G.left) k _ _ hII]
    simp only [F, rsT_sub, rsT_mul, rsT_cst _ _ _ inf_le_left, rsT_cst _ _ _ inf_le_right,
      rsT_natCast inf_le_left, rsT_natCast inf_le_right, rsT_two inf_le_left, rsT_two inf_le_right]
    rw [opV_rsT π _ dd' hdd' Θ₁ u (d i) (hd i) (pf i) (pf' i) k le_rfl (hW i) inf_le_left,
      opV_rsT π _ dd' hdd' Θ₁ u (d i') (hd i') (pf i') (pf' i') k le_rfl (hW i') inf_le_right,
      rsT_rsT (hWc i) inf_le_left, rsT_rsT (hWc i') inf_le_right, hs, hgl]
    ring
  haveI := t.semi.quasiCompact
  haveI := t.semi.separated
  haveI : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  haveI : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨tt, htt, htF⟩ := GlobalTheory.T.exists_glued_lineBundleSection_cover M hM (t.G.left.basicOpen f) W (fun i _ => j i) F (by rw [hcov, hb]) hWc hF
  obtain ⟨N, s, hs⟩ := GlobalTheory.T.exists_lineBundleSection_extend_basicOpen t.G.left M hM f tt htt
  refine ⟨c ^ N, s, pow_ne_zero N hc, fun i => ?_⟩
  have hWi : W i ≤ M.U (fun _ => j i) ⊓ t.G.left.basicOpen f := le_inf (hWc i) (hb ▸ hW i)
  refine (rsT_rsT inf_le_left hWi _).symm.trans ?_
  refine (congrArg (fun x => rsT x (W i)) (hs (fun _ => j i))).trans ?_
  rw [rsT_mul, GlobalTheory.Heat.Glue.rsT_pow' hWi, rsT_rsT le_top hWi,
    htF i, map_pow, map_pow, cst_resV]

end GlobalTheory.HeatVExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstantStatement

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

theorem _root_.GlobalTheory.T.glued_heat_operators_preserve_sections_up_to_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  first | exact @GlobalTheory.HeatVExt.heat_section | exact GlobalTheory.HeatVExt.heat_section | (intros; apply GlobalTheory.HeatVExt.heat_section <;> assumption)
end
end
