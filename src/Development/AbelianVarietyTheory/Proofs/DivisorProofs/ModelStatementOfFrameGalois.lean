module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
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
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotientStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeight

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgChainBStable

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial TensorProduct

namespace GlobalTheory.ChainStab

theorem hw_rowHom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.hw R hn ν) μ := by
  unfold Formalism.GradedWeylDivisibility.hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (Formalism.GradedWeylDivisibility.lpMinor_rowHom R _ _ _).pow _⟩

theorem homZ_of_homN {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f (fun i => (μ i : ℤ)) := by
  intro m hm
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast, h hm]

theorem applyWord_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ' : Fin r → ℤ, IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w f) μ' := by
  induction w with
  | nil => exact ⟨μ, hf⟩
  | cons x w ih =>
    obtain ⟨μ', h⟩ := ih
    exact ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_G_of_homog x.1 x.2.1 _ μ' h x.2.2⟩

theorem comp_of_homZ {R : Type} [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℤ)
    (hf : IsWeightedHomogeneous (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_wZ r n) f μ) (m : Fin r → ℕ) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = f ∨
      weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f = 0 := by
  classical
  by_cases hg : f = 0
  · right; rw [hg, map_zero]
  · obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hg
    have hN : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m0) := by
      intro d hd
      have h1 := hf hd
      have h2 := hf hm0
      rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_weight_cast] at h1 h2
      funext i
      exact_mod_cast congrFun (h1.trans h2.symm) i
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hN)]
    split_ifs
    · left; rfl
    · right; rfl

theorem weyl_comp_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  obtain ⟨μ0, h0⟩ := hw_rowHom R hn ν
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ⟩ := applyWord_homZ _ _ (homZ_of_homN _ _ h0) w
    rcases comp_of_homZ _ μ hμ m with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem tprod_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (x : ∀ i, A i) (hx : ∀ i, x i ∈ B i) :
    PiTensorProduct.tprod O x ∈ tensSub B :=
  LinearMap.mem_range.2 ⟨PiTensorProduct.tprod O (fun i => ⟨x i, hx i⟩), by rw [PiTensorProduct.map_tprod]; rfl⟩

theorem map_mem_tensSub {O : Type} [CommRing O] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module O (A i)] (B : ∀ i, Submodule O (A i)) (f : ∀ i, A i →ₗ[O] A i)
    (hf : ∀ i, ∀ x ∈ B i, f i x ∈ B i) (y : ⨂[O] i, A i) (hy : y ∈ tensSub B) :
    PiTensorProduct.map f y ∈ tensSub B := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  refine LinearMap.mem_range.2 ⟨PiTensorProduct.map (fun i => (f i).restrict (hf i)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

variable {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam : ι → ℕ → ℕ}

theorem grp_stab (s : Finset ι) (g : ι → GL (Fin N) O) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), grp O N lam g y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  have h1 : grp O N lam g = PiTensorProduct.map
      (fun i => Formalism.UG.dualWeylRep O N N (res N (lam i)) (g i)) := rfl
  rw [h1]
  refine map_mem_tensSub _ _ (fun i x hx => ?_) y hy
  unfold chainB at hx ⊢
  split_ifs at hx ⊢ with hi
  · exact Submodule.mem_top
  · exact Formalism.UG.P.weyl_module_GL_stable O N N le_rfl (res N (lam i)) (g i) x.1 hx

theorem proj_stab (s : Finset ι) (τ : ι) (w : Fin N → ℕ) (a : Module.End O (NablaT O N lam))
    (ha : IsProj O N lam τ w a) :
    ∀ y ∈ tensSub (chainB (deltaIn O N lam) s), a y ∈ tensSub (chainB (deltaIn O N lam) s) := by
  intro y hy
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, PiTensorProduct.map_tprod, map_smul]
    refine Submodule.smul_mem _ c ?_
    let x : ∀ i, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)) := fun i => (f i : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam i)))
    have hc := Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N (res N (lam τ)) w _ (x τ).2
    change a (PiTensorProduct.tprod O x) ∈ _
    rw [ha x ⟨_, hc⟩ rfl]
    apply tprod_mem_tensSub
    intro i
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      have hf := (f i).2
      unfold chainB at hf ⊢
      split_ifs at hf ⊢ with hs
      · exact Submodule.mem_top
      · exact weyl_comp_mem O le_rfl (res N (lam i)) w _ hf
    · rw [Function.update_of_ne hi]
      exact (f i).2
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ (h₁ (LinearMap.mem_range_self _ _)) (h₂ (LinearMap.mem_range_self _ _))

end GlobalTheory.ChainStab

namespace GlobalTheory.ExpFrame

open GlobalTheory.ChainStab

theorem alg_chainB_stable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (s : Finset ι) (a : alg O N lam),
    ∀ x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s), a • x ∈ tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s) := by
  intro O _ _ _ _ N ι _ _ lam s a
  let L := tensSub (chainB (Formalism.CohomologicalDescent.DepthNonnegative.deltaIn O N lam) s)
  let St : Subalgebra O (Module.End O (NablaT O N lam)) :=
    { carrier := {f | ∀ x ∈ L, f x ∈ L}
      mul_mem' := fun ha hb x hx => ha _ (hb x hx)
      add_mem' := fun ha hb x hx => L.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Module.algebraMap_end_apply]; exact L.smul_mem c hx }
  have hle : alg O N lam ≤ St := Algebra.adjoin_le (by
    rintro f (⟨g, rfl⟩ | ⟨τ, w, hf⟩)
    · exact grp_stab s g
    · exact proj_stab s τ w f hf)
  intro x hx
  exact hle a.2 x hx

end GlobalTheory.ExpFrame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifDvd

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.ExpFrame

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

theorem exists_unif_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l ≠ 0) (hu : ¬ IsUnit ((l : ℕ) : O)) :
    ∃ (ϖ : O) (n : ℕ), Irreducible ϖ ∧ ϖ ∣ (l : O) ∧ (l : O) ∣ ϖ ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  refine ⟨ϖ, n, hϖ, ?_, hn.dvd⟩
  rcases n with _ | n
  · exact absurd (hn.isUnit_iff.2 (by simp)) hu
  · exact (dvd_pow_self ϖ n.succ_ne_zero).trans hn.symm.dvd

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

section Sub

variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam) (ϖ : X.O)

abbrev Red : Type := NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ

abbrev SimpIx : Type :=
  Σ E : Submodule X.A (Red X ϖ), {N' : Submodule X.A E // IsSimpleModule X.A (E ⧸ N')}

abbrev SimpMod (μ : SimpIx X ϖ) : Type := μ.1 ⧸ μ.2.1

variable {X ϖ}

theorem exists_simpMod (Gm : Type) [AddCommGroup Gm] [Module X.A Gm] [IsSimpleModule X.A Gm]
    (h : IsSubquot X.A (Red X ϖ) Gm) :
    ∃ μ : SimpIx X ϖ, Nonempty (Gm ≃ₗ[X.A] SimpMod X ϖ μ) := by
  obtain ⟨E, ψ, hψ⟩ := h
  let e := ψ.quotKerEquivOfSurjective hψ
  haveI : IsSimpleModule X.A (E ⧸ LinearMap.ker ψ) := IsSimpleModule.congr e
  exact ⟨⟨E, LinearMap.ker ψ, inferInstance⟩, ⟨e.symm⟩⟩

end Sub

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

section SubF

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) [mT : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
  [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ mT.toSMul _]
  (m : Ideal F.T) [m.IsPrime] (ϖ : F.O)

end SubF

end GlobalTheory.ExpModel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeightStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  first | exact @GlobalTheory.HighWt.simpleSubquot_embeds | exact GlobalTheory.HighWt.simpleSubquot_embeds | (intros; apply GlobalTheory.HighWt.simpleSubquot_embeds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGalois

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lift_subquot {A V : Type} [Ring A] [AddCommGroup V] [Module A V] (S : Submodule A V) (E : Submodule A (V ⧸ S))
    (N' : Submodule A E) : ∃ (U : Submodule A V) (π : U →ₗ[A] (E ⧸ N')), Function.Surjective π ∧ ∀ x : U, (x : V) ∈ S → π x = 0 := by
  let g : E.comap S.mkQ →ₗ[A] E := (S.mkQ.domRestrict (E.comap S.mkQ)).codRestrict E (fun x => x.2)
  refine ⟨E.comap S.mkQ, N'.mkQ ∘ₗ g, fun z => ?_, fun x hx => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective S a
    have hvU : v ∈ E.comap S.mkQ := by rw [Submodule.mem_comap, hv]; exact a.2
    have hg : g ⟨v, hvU⟩ = a := Subtype.ext hv
    exact ⟨⟨v, hvU⟩, congrArg N'.mkQ hg⟩
  · have hg : g x = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero S).2 hx)
    exact (congrArg N'.mkQ hg).trans (map_zero _)



theorem winputs_of_simple {ι : Type} [DecidableEq ι] (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (W : Wts ι) (X : HidaSetting ι P.Nr W.lam) (l : ℕ) (ϖ : X.O)
    (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (hfin : Finite (X.O ⧸ Ideal.span {(l : X.O)})) (hd : (l : X.O) ∣ ϖ ^ n₀)
    (hA : X.FrameA e) (hS : HeckeStable X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam))
    (hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module X.O Gm] [Module X.A Gm] [IsScalarTower X.O X.A Gm], IsSimpleModule X.A Gm →
      (∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] Gm), Function.Surjective π ∧
        ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0) →
      ∃ (_ : Module X.T (Forms X.O X.Γ X.jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK Gm)) → ∀ τ, LatticeLink P W l τ (hw τ))) :
    WInputsLink P W X l := by
  have hsq : ∀ μ : SimpIx X ϖ, ∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] SimpMod X ϖ μ), Function.Surjective π ∧
      ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0 := by
    intro μ
    obtain ⟨U, π, h1, h2⟩ := exists_lift_subquot _ μ.1 μ.2.1
    exact ⟨U, π, h1, fun x y hxy => h2 x ⟨y, hxy⟩⟩
  have h := fun μ : SimpIx X ϖ => hQ (SimpMod X ϖ μ) μ.2.2 (hsq μ)
  choose mT hw h1 h2 h3 using h
  exact ⟨ϖ, n₀, e, SimpIx X ϖ, SimpMod X ϖ, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, mT, hw, hfin, hd, hA, ⟨hS, h1⟩, ⟨fun Gm _ _ _ hq => exists_simpMod Gm hq, h2⟩,
    fun μ _ hn τ _ => h3 μ hn τ⟩


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem winputs_frame : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), W.Ok P → (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))] [IsScalarTower F.O F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))], F.IsHecke W.lam jK (NablaT F.O P.Nr W.lam) → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) → ¬ IsUnit ((l : ℕ) : F.O) → ∀ (m : Ideal F.T) [hm : m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → haveI := hm.isPrime; WInputsLink P (reFr W fr cjj) (F.setting W.lam jK m) l := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hW hlink F hF Bk hG jK hJ _ _ hH hfin hnu m hm θ0 h0e h0b h0o
  obtain ⟨ϖ, n₀, hϖ, hϖl, hlϖ⟩ := exists_unif_dvd F.O l (Fact.out : l.Prime).ne_zero hnu
  have hanti : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
  choose e0 he0 hu0 using GlobalTheory.ExpFrame.exists_unique_isProj F.O P.Nr ι W.lam
  let e : ι → (Fin P.Nr → ℕ) → alg F.O P.Nr W.lam := fun τ w => ⟨e0 τ w, Algebra.subset_adjoin (Or.inr ⟨τ, w, he0 τ w⟩)⟩
  have hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm]
      [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm], IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm →
      ∃ (_ : Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat F.O (A := alg F.O P.Nr W.lam) F.Γ jK F.T (NablaT F.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) →
          ∀ τ, LatticeLink P (reFr W fr cjj) l τ (hw τ)) := by
    intro Gm _ _ _ _ hs hq
    obtain ⟨mT, _, hHG⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι P.Nr F W.lam jK hF hJ Gm
    obtain ⟨mu, hmu, hemb⟩ := GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight F.O P.Nr ι W.lam ϖ hϖ hanti Gm hs hq
    refine ⟨mT, fun τ => res P.Nr (mu τ), (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK Gm hH hHG).2, fun τ => ?_, fun hn =>
      GlobalTheory.T.latticeLink_of_surviving_simple_subquotient E Ω hCheb l ι inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hanti Gm hHG hs hq mu
        (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2.1⟩) hemb m θ0 h0e h0b h0o hn⟩
    obtain ⟨e', z, hp, hz⟩ := (hmu τ).2.2.2
    have hee : e τ (res P.Nr (mu τ)) = e' := Subtype.ext (hu0 τ _ _ hp).symm
    exact ⟨z, hee ▸ hz⟩
  haveI := hm.isPrime
  exact winputs_of_simple P (reFr W fr cjj) (F.setting W.lam jK m) l ϖ n₀ e hfin hlϖ
    ⟨GlobalTheory.ExpFrame.alg_chainB_stable F.O P.Nr ι W.lam, fun τ w => he0 τ w⟩
    (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK (NablaT F.O P.Nr W.lam) hH hH).1
    (fun Gm i1 i2 i3 i4 => @hQ Gm i1 i2 i3 i4)


end GlobalTheory.ExpModel

end
end
end
