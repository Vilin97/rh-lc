module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Separation.Connected
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlGen

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FreeProf

section

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem UpperTheory.V.AlgebraTools.exists_free_profinite :
    ∀ r : ℕ, ∃ (P : Type) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P) (_ : CompactSpace P)
      (_ : TotallyDisconnectedSpace P) (x : Fin r → P), TopGen (Set.range x) ∧
        ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin r → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i := by
  intro r
  let F : GrpCat.{0} := GrpCat.of (FreeGroup (Fin r))
  let P : ProfiniteGrp.{0} := completion F
  let η : FreeGroup (Fin r) →* P := (eta F).hom
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => η (FreeGroup.of i), ?_, ?_⟩
  · unfold TopGen
    have hr : Set.range (fun i => η (FreeGroup.of i)) = η '' Set.range FreeGroup.of := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
      MonoidHom.coe_range]
    exact denseRange (G := F)
  · intro G _ _ _ _ _ y
    let Q : ProfiniteGrp.{0} := ProfiniteGrp.of G
    let f0 : F ⟶ GrpCat.of Q := GrpCat.ofHom (FreeGroup.lift y)
    let L : P ⟶ Q := lift f0
    refine ⟨L.hom.toMonoidHom, L.hom.continuous, ?_⟩
    intro i
    have h : ((eta F) ≫ (forget₂ ProfiniteGrp GrpCat).map L).hom (FreeGroup.of i) =
        f0.hom (FreeGroup.of i) := by
      rw [lift_eta]
    exact h.trans FreeGroup.lift_apply_of
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GenExt

section

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_surj_over_finite :
    ∀ (P Γ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] [Group Γ] (r h : ℕ) (x : Fin (r + h) → P) (γ : Fin r → Γ) (π : P →* Γ), TopGen (Set.range x) →
      (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin (r + h) → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i) →
      Function.Surjective γ → IsOpen (π.ker : Set P) → (∀ i, π (x (Fin.castAdd h i)) = γ i) → (∀ i, π (x (Fin.natAdd r i)) = 1) →
      ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (q : G →* Γ), IsOpen (q.ker : Set G) → ∀ g : Fin r → G, (∀ i, q (g i) = γ i) →
        (∃ z : Fin h → q.ker, TopGen (Set.range z)) →
        ∃ f : P →* G, Continuous f ∧ Function.Surjective f ∧ q.comp f = π ∧ ∀ i, f (x (Fin.castAdd h i)) = g i := by
  intro P Γ _ _ _ _ _ _ r h x γ π hden huniv hγ hπo hπl hπr G _ _ _ _ _ q hqo g hg hz
  obtain ⟨z, hzd⟩ := hz
  obtain ⟨f, hf, hfx⟩ := huniv G (Fin.append g (fun j => (z j : G)))
  have hfl : ∀ i, f (x (Fin.castAdd h i)) = g i := fun i => by
    rw [hfx, Fin.append_left]
  have hfr : ∀ j, f (x (Fin.natAdd r j)) = z j := fun j => by
    rw [hfx, Fin.append_right]
  refine ⟨f, hf, ?_, ?_, hfl⟩
  · haveI : T2Space G := inferInstance
    have hRc : IsClosed (Set.range f) := (isCompact_range hf).isClosed
    have hker : ∀ k : q.ker, (k : G) ∈ Set.range f := by
      let S : Set q.ker := Subtype.val ⁻¹' Set.range f
      have hSc : IsClosed S := hRc.preimage continuous_subtype_val
      have hsub : ((Subgroup.closure (Set.range z) : Subgroup q.ker) : Set q.ker) ⊆ S := by
        have : Subgroup.closure (Set.range z) ≤ f.range.comap q.ker.subtype := by
          rw [Subgroup.closure_le]
          rintro _ ⟨j, rfl⟩
          exact ⟨x (Fin.natAdd r j), hfr j⟩
        intro a ha
        exact this ha
      have hdS : Dense S := hzd.mono hsub
      intro k
      have : k ∈ S := by
        rw [← hSc.closure_eq, hdS.closure_eq]
        trivial
      exact this
    intro a
    obtain ⟨i, hi⟩ := hγ (q a)
    have hmem : (g i)⁻¹ * a ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg i, hi, inv_mul_cancel]
    obtain ⟨p1, hp1⟩ := hker ⟨_, hmem⟩
    refine ⟨x (Fin.castAdd h i) * p1, ?_⟩
    rw [map_mul, hfl, hp1]
    simp
  · set φ := q.comp f with hφ
    have hgen : Set.EqOn φ π (Set.range x) := by
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hφ, hfl, hg, hπl]
      | right j =>
        simp only [hφ, MonoidHom.comp_apply, hfr, hπr]
        exact (z j).2
    have hcl : Set.EqOn φ π (Subgroup.closure (Set.range x)) := MonoidHom.eqOn_closure hgen
    have hφo : IsOpen (φ.ker : Set P) := by
      have : (φ.ker : Set P) = f ⁻¹' (q.ker : Set G) := by
        ext a
        simp [hφ]
      rw [this]
      exact hqo.preimage hf
    ext p
    let V : Set P := (fun a => p⁻¹ * a) ⁻¹' ((π.ker : Set P) ∩ (φ.ker : Set P))
    have hVo : IsOpen V := (hπo.inter hφo).preimage (continuous_const.mul continuous_id)
    have hpV : p ∈ V := by
      simp [V]
    obtain ⟨d, ⟨hd1, hd2⟩, hdD⟩ := hden.inter_open_nonempty V hVo ⟨p, hpV⟩
    have e1 : π (p⁻¹ * d) = 1 := hd1
    have e2 : φ (p⁻¹ * d) = 1 := hd2
    rw [map_mul, map_inv, inv_mul_eq_one] at e1 e2
    rw [e2, hcl hdD, ← e1]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SysCover

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sys_cover :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → ∃ (Ph : Type) (_ : Group Ph) (_ : TopologicalSpace Ph) (_ : IsTopologicalGroup Ph) (_ : CompactSpace Ph) (_ : TotallyDisconnectedSpace Ph) (π : ∀ N, Ph →* (T.GN N).Γ) (ct : Ph), TopFG Ph ∧ (∀ N, Continuous (π N) ∧ Function.Surjective (π N) ∧ π N ct = (T.GN N).c) ∧ ∀ N N' g, (T.h N).p (π N g) * ((T.h N').p (π N' g))⁻¹ ∈ T.H := by
  intro l _ L G0 T hT
  classical
  let H0 : Subgroup G0.Γ := (T.H : Subgroup G0.Γ)
  have hH0open : IsOpen (H0 : Set G0.Γ) := T.H.isOpen
  obtain ⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n → G0.Γ ⧸ H0, Function.Surjective e := by
    obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (G0.Γ ⧸ H0)
    exact ⟨n, eq.symm, eq.symm.surjective⟩
  let lift : G0.Γ ⧸ H0 → G0.Γ := Function.surjInv QuotientGroup.mk_surjective
  have hlift : ∀ y, (QuotientGroup.mk (lift y) : G0.Γ ⧸ H0) = y :=
    Function.surjInv_eq QuotientGroup.mk_surjective
  let yc : Fin (n + 1) → G0.Γ := Fin.cons G0.c (fun i => lift (e i))
  let γ : Fin (n + 1) → G0.Γ ⧸ H0 := fun i => QuotientGroup.mk (yc i)
  have hγ : Function.Surjective γ := by
    intro y
    obtain ⟨i, rfl⟩ := he y
    exact ⟨i.succ, by simp [γ, yc, hlift]⟩
  obtain ⟨P, iG, iT, iTG, iC, iTD, x, hx, hfree⟩ := exists_free_profinite (n + 1 + T.hb)
  obtain ⟨f0, hf0c, hf0x⟩ := hfree G0.Γ (Fin.append yc (fun _ => 1))
  let π0 : P →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp f0
  have hπ0ker : IsOpen (π0.ker : Set P) := by
    have : (π0.ker : Set P) = f0 ⁻¹' (H0 : Set G0.Γ) := by
      ext g
      simp [π0, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [this]
    exact hH0open.preimage hf0c
  have hcast : ∀ i : Fin (n + 1), π0 (x (Fin.castAdd T.hb i)) = γ i := by
    intro i
    simp [π0, γ, hf0x, Fin.append_left]
  have hnat : ∀ i : Fin T.hb, π0 (x (Fin.natAdd (n + 1) i)) = 1 := by
    intro i
    simp [π0, hf0x, Fin.append_right]
  have key : ∀ N : ℕ, ∃ f : P →* (T.GN N).Γ, Continuous f ∧ Function.Surjective f ∧
      ((QuotientGroup.mk' H0).comp (T.h N).p).comp f = π0 ∧
      f (x (Fin.castAdd T.hb 0)) = (T.GN N).c := by
    intro N
    let p := (T.h N).p
    let q : (T.GN N).Γ →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp p
    let HN : Subgroup (T.GN N).Γ := H0.comap p
    haveI : HN.Normal := Subgroup.Normal.comap inferInstance p
    have hqker : q.ker = HN := by
      ext g
      simp [q, HN, p, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hHNopen : IsOpen (HN : Set (T.GN N).Γ) := hH0open.preimage (T.h N).cont
    have hqopen : IsOpen (q.ker : Set (T.GN N).Γ) := by rw [hqker]; exact hHNopen
    let g : Fin (n + 1) → (T.GN N).Γ :=
      Fin.cons (T.GN N).c (fun i => Function.surjInv (T.h N).surj (yc i.succ))
    have hg : ∀ i, q (g i) = γ i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [q, g, γ, yc, p, (T.h N).c]
      · simp [q, g, γ, p, Function.surjInv_eq (T.h N).surj]
    have hz : ∃ z : Fin T.hb → ↥q.ker, TopGen (Set.range z) := by
      rw [hqker]
      have hPL := hT.2 N
      have hfin := T.finN N
      exact (pl_gen l (T.GN N).Γ HN hHNopen hPL hfin.1).2 T.hb hfin.2
    obtain ⟨f, hfc, hfs, hfq, hfx⟩ :=
      exists_surj_over_finite P (G0.Γ ⧸ H0) (n + 1) T.hb x γ π0 hx hfree hγ hπ0ker hcast hnat
        (T.GN N).Γ q hqopen g hg hz
    exact ⟨f, hfc, hfs, hfq, by rw [hfx 0]; simp [g]⟩
  choose F hFc hFs hFq hFx using key
  refine ⟨P, iG, iT, iTG, iC, iTD, F, x (Fin.castAdd T.hb 0), ⟨Set.range x, Set.finite_range x, hx⟩,
    fun N => ⟨hFc N, hFs N, hFx N⟩, ?_⟩
  intro N N' g
  have h1 := congrArg (fun φ => φ g) (hFq N)
  have h2 := congrArg (fun φ => φ g) (hFq N')
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2
  have h3 : (QuotientGroup.mk ((T.h N).p (F N g)) : G0.Γ ⧸ H0) = QuotientGroup.mk ((T.h N').p (F N' g)) := by
    rw [h1, h2]
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h3
  exact h3
end
end
