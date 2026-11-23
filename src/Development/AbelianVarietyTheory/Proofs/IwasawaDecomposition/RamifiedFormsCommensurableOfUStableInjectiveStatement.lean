module

public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
public import Formalism.LocalRingCardinality.Lemmas
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

section General

end General

variable (D : D7) (u : D.what₂.Word)

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

end GlobalTheory.LevelIndexCompare

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelCommensurable

theorem exists_nsmul_map_mem {K V W : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) W) (hA : A.FG) (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤)
    (f : W →ₗ[K] V) : ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, n • f x ∈ L := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have h : ∀ x : W, ∃ n : ℕ, n ≠ 0 ∧ n • f x ∈ L := fun x =>
    GlobalTheory.Mem.Full.exists_nsmul_mem_of_span L (f x) (by rw [hL]; trivial)
  choose c hc0 hc using h
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_coe.1 hy)
    rw [hk, mul_comm, mul_smul]
    exact L.toAddSubmonoid.nsmul_mem (hc y) k
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), smul_add]; exact L.add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, map_smul, smul_comm, algebraMap_smul]
    exact L.smul_mem r hy


open GlobalTheory.LevelIndexCompare GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks in
theorem commensurable : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  classical
  intro D u hst hinj w
  have hex : ∀ v, ∃ g, IsScaledU D u w v g := fun v => (exists_isScaledU_iff D u w v).2 (hst v)
  choose g hg using hex
  haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  have hgi : ∀ v, IsUnit (g v) := by
    intro v
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hg v x
    rw [hx, Submodule.coe_zero, map_zero] at h1
    have h2 := (smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ (T_ne_zero D u))
    have h3 := hinj v _ x.2 h2
    exact Subtype.ext ((D.fm u).emb_inj 0 (h3.trans (map_zero _).symm))
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hGu : IsUnit G := by
    refine IsUnit.pow _ (List.prod_isUnit fun a ha => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact hgi v
  obtain ⟨H, hH⟩ := hGu.exists_right_inv
  have hmem : ∀ x, D.nuIn u x ∈ (D.fm u).ramSub := fun x => D.nuIn_range u ▸ ⟨x, rfl⟩
  let e : (D.div.Nu u).V →ₗ[D.what₂.LL] (D.fm u).ramSub := LinearMap.codRestrict _ (D.nuIn u) hmem
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ H ∘ₗ e)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e)
  refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)]
    have hL : (((n₁ * n₂) • H (e x) : (D.fm u).ramSub) : LT.Vl D u 0) ∈ ((D.fm u).lat 0).L := by
      rw [mul_comm, mul_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
      exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem (h₁ x hx) n₂
    refine ⟨⟨_, ⟨Submodule.subset_span hL, ((n₁ * n₂) • H (e x)).2⟩⟩, ?_⟩
    show _ = ((G ((n₁ * n₂) • H (e x)) : (D.fm u).ramSub) : LT.Vl D u 0)
    rw [map_nsmul G, ← Module.End.mul_apply, hH, map_nsmul]
    rfl
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨s, hs, hsy⟩ := D.inLoc_of_mem_locW w _ _ y.2.1
    obtain ⟨z, hz⟩ : (y : LT.Vl D u 0) ∈ LinearMap.range (D.nuIn u) := by
      rw [D.nuIn_range u]; exact y.2.2
    have hsm : ∀ t, D.nuIn u (s • t) = s • D.nuIn u t := fun t =>
      map_smul ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) s t
    have hzM : s • z ∈ DV.MramL D u := by
      show D.nuIn u (s • z) ∈ ((D.fm u).lat 0).L
      rw [hsm, hz]; exact hsy
    have h3 := h₂ _ hzM
    have hez : e z = incl D u w y := Subtype.ext hz
    have h4 : ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e) (s • z) = s • D.nuIn u x := by
      rw [← algebraMap_smul D.what₂.LL s z, map_smul, algebraMap_smul, hy]
      show s • ((G (e z) : (D.fm u).ramSub) : LT.Vl D u 0) = _
      rw [hez]
    rw [h4] at h3
    refine ⟨s, hs, ?_⟩
    show D.nuIn u (s • (n₁ * n₂) • x) ∈ ((D.fm u).lat 0).L
    rw [hsm, map_nsmul, smul_comm, mul_smul]
    exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem h3 n₁

end GlobalTheory.LevelCommensurable
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  first | exact @GlobalTheory.LevelCommensurable.commensurable | exact GlobalTheory.LevelCommensurable.commensurable | (intros; apply GlobalTheory.LevelCommensurable.commensurable <;> assumption)
end
end
