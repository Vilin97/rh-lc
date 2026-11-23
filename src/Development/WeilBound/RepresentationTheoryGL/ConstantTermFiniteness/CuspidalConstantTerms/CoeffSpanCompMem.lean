module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CasimirAnnihilatedCuspFormsFiniteDimensionalStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteType
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
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermRestrictSmoothModerate
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCuspFunSlice
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothAutomorphicDerivativeGrowthStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.StandardThreeBlockIndexStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteTypeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.constant_term_parabolic_eigenfunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∃ A : D.what₂.Tau → ℕ → List ℂ, ∀ ψ ∈ formsOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → ∀ τ k, (A τ k).foldr (fun a f => gelf θ V' τ k f - a • f) (fun h => ψ (s h * y)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.gelf_slices_monic | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.gelf_slices_monic | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCentre.gelf_slices_monic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermRestrictSmoothModerateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.frame_adapted_subspace_unitary_group : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → ∀ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∃ (ε' : D.what₂.Tau → Fin V'.rank → Bool) (fr' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (j : ∀ τ, Formalism.REAL.KG (ε' τ) →* Formalism.REAL.KG (ε τ)), IsFrameFam V' ε' fr' ∧ (∀ τ, Continuous (j τ)) ∧ ∀ τ k, s (kAt θ V' τ (ε' τ) (fr' τ) k) = kAt θ V τ (ε τ) (fr τ) (j τ k) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames.exists_restricted_frame <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbedding

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
  starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg

    simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]

    rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]

      simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2

      simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceUnitaryEmbeddingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.exists_orthogonal_hermitian_subspace : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WittCompl.exists_compl | exact GlobalTheory.CompanionTheory.WittCompl.exists_compl | (intros; apply GlobalTheory.CompanionTheory.WittCompl.exists_compl <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.CoeffSpanCompMem

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem coeffSpan_comp_mem {K K' W : Type} [Group K] [Group K'] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) (j : K' →* K) {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (f ∘ j) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j) := by
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨ℓ, w, rfl⟩ := h
    exact Submodule.subset_span ⟨ℓ, w, rfl⟩
  | zero => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).zero_mem
  | add a b _ _ ha hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).add_mem ha hb
  | smul a b _ hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).smul_mem a hb

theorem finite_slices_core : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) 1)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hXY T _hT hAd
  obtain ⟨V', ι, hι, hran⟩ := GlobalTheory.T.exists_orthogonal_hermitian_subspace D V m X Y hXY T
  obtain ⟨s, hsc, hsrel, hsq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have hs : ∀ h, EmbRel V V' ι (s h) h := fun h => (hsrel h (s h)).2 rfl
  obtain ⟨hsu, hsurj, hsf⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hXY T V' ι hι hran s hs
  obtain ⟨ε', fr', j, hfr', hj, hk⟩ := GlobalTheory.T.frame_adapted_subspace_unitary_group D θ hθ V ε fr hfr m X Y hXY T hAd V' ι hι hran s hs
  obtain ⟨A, hA⟩ := GlobalTheory.T.constant_term_parabolic_eigenfunction D θ hθ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs
  let U' : Subgroup (GA D V') := U.comap s
  have hU' : IsOpen (U' : Set (GA D V')) := hU.preimage hsc
  let ρ' : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε' τ)) (W τ) := fun τ => (ρ τ).comp (j τ)
  have hρ' : ∀ τ, IsContRep (ρ' τ) := fun τ ℓ w => (hρ τ ℓ w).comp (hj τ)
  let B : Set (GA D V' → ℂ) := {φ | IsAutFunSm θ V' φ ∧ (∀ u ∈ U', u ∈ GfC V' → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V' τ (ε' τ) (fr' τ) (ρ' τ) φ) ∧ IsCuspFun V' φ ∧
    ∀ τ, (A τ 1).foldr (fun a f => gelf θ V' τ 1 f - a • f) φ = 0}
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ B) :=
    GlobalTheory.T.constant_term_parabolic_finite_type D θ hθ V' U' hU' ε' fr' hfr' W ρ' hρ' (fun τ => A τ 1)
  have hmem : ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T,
      (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → (fun h => ψ (s h * y)) ∈ B := by
    intro ψ hψ y hy hyc
    obtain ⟨h1, h2, h3, _⟩ := hψ.1
    have hcomm : ∀ h, s h * y = y * s h := fun h => hyc _ (hsu h)
    obtain ⟨hsm, hgr⟩ := GlobalTheory.T.constant_term_restrict_smooth_moderate D θ hθ V V' ι hι s hs _ ψ h1 y hcomm
    have hAF : IsAutFun V' (fun h => ψ (s h * y)) :=
      { left := fun γ hγ g => by
          have hm : s γ ∈ leftSub V X Y T :=
            Subgroup.mem_sup_right ⟨hsq γ hγ, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hsu γ)⟩
          simp only [map_mul]
          rw [mul_assoc]
          exact h1.left _ hm _
        level := ⟨U', hU', fun k hk hk' g => by
          simp only [map_mul]
          rw [mul_assoc, hcomm k, ← mul_assoc]
          exact h2 _ hk (hsf k hk') _⟩
        cont := h1.cont.comp (hsc.mul continuous_const) }
    refine ⟨GlobalTheory.T.smooth_automorphic_derivative_growth D θ hθ V' _ hAF hsm hgr (fun τ k => ⟨A τ k, hA ψ hψ.1 y hy hyc τ k⟩),
      ?_, fun τ x => ?_,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.isCuspFun_slice D θ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs ψ hψ y hy hyc, fun τ => hA ψ hψ.1 y hy hyc τ 1⟩
    · intro k hk hk' g
      simp only [map_mul]
      rw [mul_assoc, hcomm k, ← mul_assoc]
      exact h2 _ hk (hsf k hk') _
    · have e : (fun k => ψ (s (x * kAt θ V' τ (ε' τ) (fr' τ) k) * y)) =
          (fun k0 => ψ ((s x * y) * kAt θ V τ (ε τ) (fr τ) k0)) ∘ j τ := by
        funext k
        simp only [Function.comp, map_mul]
        rw [mul_assoc, hcomm, ← mul_assoc, ← hk τ k]
      rw [e]
      exact coeffSpan_comp_mem (ρ τ) (j τ) (h3 τ (s x * y))
  let s' : GA D V' → uPart D.sp.cm.sig V.gram X Y T := fun h => ⟨s h, hsu h⟩
  have hs' : Function.Surjective s' := fun g => by
    obtain ⟨h, hh⟩ := hsurj g.1 g.2
    exact ⟨h, Subtype.ext hh⟩
  let Φ := LinearMap.funLeft ℂ ℂ s'
  have hΦ : Function.Injective Φ := LinearMap.funLeft_injective_of_surjective _ _ _ hs'
  set P := Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T)
    (levi D.sp.cm.sig V.gram X Y T) 1)
  have hle : P.map Φ ≤ Submodule.span ℂ B := by
    rw [Submodule.map_span_le]
    rintro f ⟨ψ, hψ, y, hy, hyc, rfl⟩
    apply Submodule.subset_span
    have := hmem ψ hψ y hy hyc
    convert this using 1
    funext h
    simp [Φ, s', LinearMap.funLeft]
  haveI : FiniteDimensional ℂ (P.map Φ) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective Φ hΦ P).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg
end
end
end
