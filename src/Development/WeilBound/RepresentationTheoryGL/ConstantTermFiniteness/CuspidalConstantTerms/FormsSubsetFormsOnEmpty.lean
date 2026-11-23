module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsExtendWitt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInheritedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowthStatement
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteDimensionalOfParts
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep

open MeasureTheory GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem finiteDimensional_coeffs {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  let T : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (K → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w => fun k => ℓ (ρ k w))
      (fun ℓ₁ ℓ₂ w => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
      (fun ℓ w₁ w₂ => by funext k; simp)
      (fun a ℓ w => by funext k; simp)
  have hle : coeffSpan ρ ≤ LinearMap.range (TensorProduct.lift T) := by
    unfold coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ⊗ₜ w, by simp [T]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → K) (a : ι → K → ℂ), (∀ i, a i ∈ A) ∧
      ∀ f ∈ A, ∀ k, f k = ∑ i, f (p i) * a i k := by
  classical
  let E : K → Module.Dual ℂ A := fun k => (LinearMap.proj k).comp A.subtype
  have htop : Submodule.span ℂ (Set.range E) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range E)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      funext k
      have h := hf (E k) (Submodule.subset_span ⟨k, rfl⟩)
      simpa [E] using h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range E)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range E)
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Module.Dual ℂ A)) := by
    rw [Subtype.range_coe, hbspan, htop]
  let B : Module.Basis b ℂ (Module.Dual ℂ A) := Module.Basis.mk hbli hbtop
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hp : ∀ i : b, ∃ k, E k = (i : Module.Dual ℂ A) := fun i => hbsub i.2
  choose p hpE using hp
  let a : b → A := fun i => (Module.evalEquiv ℂ A).symm (B.coord i)
  refine ⟨b, inferInstance, p, fun i k => (a i : K → ℂ) k, fun i => (a i).2, ?_⟩
  intro f hf k
  have key := B.sum_dual_apply_smul_coord (Module.evalEquiv ℂ A ⟨f, hf⟩)
  have key2 : (⟨f, hf⟩ : A) = ∑ i, (B i ⟨f, hf⟩) • a i := by
    apply (Module.evalEquiv ℂ A).injective
    conv_lhs => rw [← key]

    rw [map_sum]
    simp only [map_smul, a, LinearEquiv.apply_symm_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hk := congrArg (fun g : A => (g : K → ℂ) k) key2
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  rw [hk]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hBi : B i = (i : Module.Dual ℂ A) := by simp [B]
  rw [hBi, ← hpE i]
  rfl

theorem hasTypeAt_of_isConstAlong : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  intro D θ V m X Y hW S T hST τ e P W _ _ _ ρ φ c hφ hty hc
  classical
  have hst := GlobalTheory.StdPar.constAlong_cocompact_unique_stages (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) hW
  obtain ⟨hcoc, μ, 𝓕, hμ, h𝓕, h1⟩ := hst.1 T
  haveI := hμ
  have hcI := hc μ 𝓕 hμ h𝓕 h1
  haveI := finiteDimensional_coeffs ρ
  obtain ⟨ι, _, p, a, ha, hrep⟩ := exists_interp (coeffSpan ρ)
  have hcoc' : GlobalTheory.Cusp.Cocompact (GQ V ⊓ unip D.sp.cm.sig V.gram X T) (unip D.sp.cm.sig V.gram X T) := by
    obtain ⟨K, hK, hKc⟩ := hcoc
    refine ⟨K, hK, fun n => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKc n
    refine ⟨γ, ?_, hγK⟩
    rw [Subgroup.inf_subgroupOf_right]
    exact hγ
  have h𝓕' : IsFundamentalDomain ((GQ V ⊓ unip D.sp.cm.sig V.gram X T).subgroupOf
      (unip D.sp.cm.sig V.gram X T)) 𝓕 μ := by
    rw [Subgroup.inf_subgroupOf_right]
    exact h𝓕
  haveI hdQ : DiscreteTopology ↥(GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram) := inferInstance
  haveI hdisc : DiscreteTopology ↥(GQ V ⊓ unip D.sp.cm.sig V.gram X T) :=
    DiscreteTopology.of_subset hdQ (fun y hy => hy.1)
  have hint : ∀ g : GA D V, IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => φ ((u : GA D V) * g)) 𝓕 μ := by
    intro g
    exact GlobalTheory.Cusp.Cocompact.integrableOn hcoc' h𝓕'
      (fun γ hγ g' => hφ.left γ (ratPts_unip_le_leftSub D V m X Y hW S T hST hγ) g') hφ.cont g
  intro x
  have hfun : (fun k => c (x * kAt θ V τ e P k)) = ∑ i, c (x * kAt θ V τ e P (p i)) • a i := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcI (x * kAt θ V τ e P k)]
    have hpt : ∀ u : unip D.sp.cm.sig V.gram X T, φ ((u : GA D V) * (x * kAt θ V τ e P k)) =
        ∑ i, φ ((u : GA D V) * (x * kAt θ V τ e P (p i))) * a i k := by
      intro u
      have h := hrep _ (hty ((u : GA D V) * x)) k
      simpa [mul_assoc] using h
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => Integrable.mul_const (hint _) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, hcI]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha i)

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicKFiniteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.constant_term_parabolic_K_finite : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → ∀ (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → HasTypeAt θ V τ e P ρ φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → HasTypeAt θ V τ e P ρ c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.TypeKeep.hasTypeAt_of_isConstAlong <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem _root_.GlobalTheory.T.rational_unipotent_le_parabolic : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.ratPts_unip_le_leftSub <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FormsSubsetFormsOnEmpty

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

section Main

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem host_facts (D : D7) (V : HSp D) : IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ IsHermND D.sp.cm.sig V.gram :=
  let h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  ⟨h.1, h.2 V⟩

theorem forms_subset_formsOn_empty (hθ : IsInfFam θ) :
    forms θ V U ε fr ρ c ⊆ formsOn θ V X Y ∅ U ε fr ρ c := by
  rintro φ ⟨h1, h2, h3, h4⟩
  have hle : (leftSub V X Y ∅ : Set (GA D V)) ⊆ GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram := by
    have : leftSub V X Y ∅ ≤ GQ V := by
      refine sup_le ?_ inf_le_left
      rw [unip_empty]
      exact bot_le
    exact this
  exact ⟨IsSmModOn.of_isSmoothModerate (GlobalTheory.SiegelSet.isSmoothModerate_of_isAutFunSm hθ h1) hle, h2, h3, h4⟩

theorem constAlong_mem_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) {S T : Finset (Fin m)} (hST : S ⊆ T) (hT : T.Nonempty)
    {φ a : GA D V → ℂ} (hφ : φ ∈ formsOn θ V X Y S U ε fr ρ c) (ha : IsConstAlong D.sp.cm.sig V.gram X T φ a) :
    a ∈ formsOn θ V X Y T U ε fr ρ c := by
  obtain ⟨h1, h2, h3, h4⟩ := hφ
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  obtain ⟨m1, m2⟩ := GlobalTheory.T.constant_term_moderate_growth_inherited D V m X Y hW S T hST hT φ a h1 ha
  obtain ⟨-, μ, 𝓕, b1, b2, b3⟩ := st.1 T
  have hleft : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ :=
    ⟨fun γ hγ g => h1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW S T hST hγ) g, h1.level, h1.cont, h1.smooth, h1.growth⟩
  refine ⟨m1, fun u hu hu' g => ?_, fun τ => GlobalTheory.T.constant_term_parabolic_K_finite D θ V m X Y hW S T hST τ (ε τ) (fr τ) (W τ) (ρ τ) φ a h1 (h3 τ) ha,
    fun τ k => ?_⟩
  · rw [ha μ 𝓕 b1 b2 b3 (g * u), ha μ 𝓕 b1 b2 b3 g]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x => ?_)
    change φ (_ * (g * u)) = φ (_ * g)
    rw [← mul_assoc, h2 u hu hu']
  · have g1 := GlobalTheory.T.constant_term_smooth_moderate_growth D θ hθ V m X Y hW T φ a hleft m1.smooth m2 τ k
    rw [h4 τ k] at g1
    have g2 : IsConstAlong D.sp.cm.sig V.gram X T (c τ k • φ) (c τ k • a) := fun μ 𝓕 b1 b2 b3 g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [ha μ 𝓕 b1 b2 b3 g, MeasureTheory.integral_const_mul]
    exact st.2.2.1 T _ _ _ g1 g2

theorem finite_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ) (hU : IsOpen (U : Set (GA D V)))
    (hfr : IsFrameFam V ε fr) (hρ : ∀ τ, IsContRep (ρ τ)) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) :
    ∀ (j : ℕ) (T : Finset (Fin m)), T.Nonempty → Tᶜ.card = j →
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c)) := by
  classical
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro T hT hj
  set A := Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c) with hA
  have hmem : ∀ f : A, f.1 ∈ formsOn θ V X Y T U ε fr ρ c := fun f => mem_formsOn_of_mem_span hθ f.2
  have hl : ∀ f : A, ∀ T' : Finset (Fin m), T ⊆ T' → GlobalTheory.AutomorphicL2Unitary.LeftInv
      (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X T') f.1 := fun f T' h γ hγ g =>
    (hmem f).1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW T T' h hγ) g

  have key : ∀ k : {k // k ∉ T}, ∃ L : A →ₗ[ℂ] Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c),
      ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1 (L f).1 := by
    intro k
    have hsub : T ⊆ insert k.1 T := Finset.subset_insert _ _
    haveI := locallyCompact_unip hcm hJ hW (insert k.1 T)
    have cS := cocompact_unip_std hcm hJ hW (insert k.1 T)
    have cS' := cocompact_ratPts_inf le_rfl cS
    have hc : ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1
        (GlobalTheory.Cusp.constTermOn (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X (insert k.1 T))
          (unip D.sp.cm.sig V.gram X (insert k.1 T)) f.1) := fun f =>
      (isConstTermOn_iff_ratPts_inf le_rfl cS (hl f _ hsub)).2 rfl
    refine ⟨{ toFun := fun f => ⟨_, Submodule.subset_span
                (constAlong_mem_formsOn hθ hW hsub (Finset.insert_nonempty _ _) (hmem f) (hc f))⟩
              map_add' := fun a b => Subtype.ext (funext fun x =>
                cS'.constTermOn_add (hl a _ hsub) (hmem a).1.cont (hl b _ hsub) (hmem b).1.cont x)
              map_smul' := fun a f => Subtype.ext (funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x) }, hc⟩
  choose L hL using key
  have hfin : ∀ k : {k // k ∉ T},
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := fun k => by
    have hlt : (insert k.1 T)ᶜ.card < j := by
      rw [← hj]
      refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hx ⊢
        exact hx.2
      · have := h (Finset.mem_compl.2 k.2)
        simp at this
    exact ih _ hlt _ (Finset.insert_nonempty _ _) rfl
  let Ψ : A →ₗ[ℂ] (∀ k : {k // k ∉ T}, Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := LinearMap.pi L
  have hker : ∀ f : A, Ψ f = 0 → ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' f.1 0 := by
    intro f hf T' hT'
    obtain ⟨k, hk, hkT⟩ := Finset.exists_of_ssubset hT'
    have h0 : (L ⟨k, hkT⟩ f).1 = 0 := congrArg Subtype.val (congrFun hf ⟨k, hkT⟩)
    have h1 := hL ⟨k, hkT⟩ f
    rw [h0] at h1
    exact st.2.2.2.2 T' (insert k T) f.1 0 0 (Finset.insert_subset hk hT'.1) (hmem f).1.cont
      (fun γ hγ hγ' g => hl f T' hT'.1 γ ⟨hγ, hγ'⟩ g) h1 (isConstAlong_const _ _ _ _ 0)
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg.finite_cuspOn D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by
    let ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧
        ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0} :=
      { toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective ι fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
  haveI := hfin
  haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)

end Main

theorem finite_constTerm : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.Published.AutFin.IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ c : D.what₂.Tau → ℕ → ℂ, ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C), FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) '' GlobalTheory.Published.AutFin.forms θ V U ε fr ρ c)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c r C hC
  obtain ⟨hcm, hJ⟩ := host_facts D V
  obtain ⟨hr, hi, hg⟩ := id hC
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm, X, Y, hW, hX⟩ := GlobalTheory.WittExt.exists_isWittFrame_initCols D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ r C hi hg
  have hfin := finite_formsOn (c := c) (U := U) hθ hU hfr hρ hW _ {(⟨r, hm⟩ : Fin m)} (Finset.singleton_nonempty _) rfl
  haveI := hfin
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (formsOn θ V X Y {(⟨r, hm⟩ : Fin m)} U ε fr ρ c))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, hφ, rfl⟩
  refine Submodule.subset_span ?_
  have h0 := forms_subset_formsOn_empty (X := X) (Y := Y) hθ hφ
  refine constAlong_mem_formsOn hθ hW (Finset.empty_subset _) (Finset.singleton_nonempty _) h0 ?_
  rw [isConstAlong_singleton hW, hX, GlobalTheory.UAut.isConstTerm_iff]
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram C := GlobalTheory.Cusp.NA_frameFlag hC
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC)) φ
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) φ) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hφ.1.left g, MeasureTheory.Measure.real, b3]
    simp
  exact e ▸ h1

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg
end
end
end
