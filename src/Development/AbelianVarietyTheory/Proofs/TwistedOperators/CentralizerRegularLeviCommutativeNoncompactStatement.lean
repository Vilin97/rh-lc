module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PicardGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalUnitaryScalingWittFrameStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeightsStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

theorem _root_.GlobalTheory.T.commute_of_wittFrame_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  first | exact @GlobalTheory.Cusp.WeightCommute.commute_of_weights | exact GlobalTheory.Cusp.WeightCommute.commute_of_weights | (intros; apply GlobalTheory.Cusp.WeightCommute.commute_of_weights <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPowArchProjNotMemOfEigenvalueTwo

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Twist

open scoped TensorProduct Matrix



theorem exists_pow_projArch_not_mem_of_eigen_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  intro D V g x hx hg w K hK
  classical
  set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def
  have hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c := by
    have h1 := congrArg (fun y => ⇑(V.frame.repr y)) hg
    simp only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin] at h1
    exact h1
  have hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    have : V.frame.repr x = 0 := Finsupp.ext h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)

  let ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E := inclR (F := D.host.F) w.Completion
  let Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion :=
    (TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map LinearMap.id φ
  have hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e) := by
    intro e
    simp [Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]
  have : IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing w.Completion _
  have hΛ : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  let f : GArch D.sp.cm.sig V.gram w → w.Completion := fun h =>
    Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)
  have hm : Continuous fun h : GArch D.sp.cm.sig V.gram w =>
      (matHom _ D.sp.cm.sig V.gram h).val :=
    Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous
  have hf : Continuous f := hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι :=
    fun γ => rfl
  have hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) =
      algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j)) := by
    intro n
    have e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι := he (g ^ n)
    simp only [f]
    rw [e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]
    congr 1
    rw [show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat],
      map_smul, smul_eq_mul]
  have hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a := fun a => by
    rw [show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]]
    exact AbsoluteValue.Completion.norm_coe _
  have hpos : 0 < w (φ (c j)) := (InfinitePlace.pos_iff).2 hφ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun hmem => ?_⟩
  rw [show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from
    projArch_ratEmb _ _ w _] at hmem
  have h1 := hC _ hmem
  rw [hval, hnorm, map_mul, map_pow] at h1
  have h2 : w (2 : D.host.F) = 2 := by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [h2] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

end GlobalTheory.Twist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPowArchProjNotMemOfEigenvalueTwoStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

theorem _root_.GlobalTheory.T.exists_pow_archProj_not_mem_of_eigenvalue_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  first | exact @GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two | exact GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two | (intros; apply GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompact

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.LeviCent

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extSub act)
open Matrix
open scoped TensorProduct

theorem nontrivial_AF (F : Type) [Field F] [NumberField F] : Nontrivial (AF F) := ⟨⟨0, 1, fun e => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact zero_ne_one ((map_zero (evInf F w)).symm.trans ((congrArg (evInf F w) e).trans (map_one _)))⟩⟩

theorem exists_aeval_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) :
    ∃ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X],
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 = aeval (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1 p := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field γ.1.1 hγ
  refine GlobalTheory.Orb.exists_aeval_of_cyclic (v := inclR (AF D.host.F) ∘ v) ?_ ?_
  · change IsUnit (GlobalTheory.ClassParam.krylov (γ.1.1.map (inclR (AF D.host.F))) _).det
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map _
  · have := congrArg (fun x => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram x).1) (mem_cent.1 hg)
    simp only [map_mul, Units.val_mul] at this
    exact this

theorem mem_parab_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) (W : Submodule D.host.E V.V)
    (h : rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W) :
    g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W := by
  set S := extSub (F := D.host.F) V (AF D.host.F) W
  have hs : ∀ y, y ∈ S ↔ act D.sp.cm V (rat V γ) y ∈ S := h
  set M := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1
  have hM : ∀ y ∈ S, M *ᵥ y ∈ S := fun y hy => (hs y).1 hy
  have hp : ∀ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X], ∀ y ∈ S, aeval M p *ᵥ y ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro y hy
      rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ a hy
    | add p q hp hq =>
      intro y hy
      rw [map_add (f := _), Matrix.add_mulVec]
      exact add_mem (hp y hy) (hq y hy)
    | monomial n a ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
      exact ih _ (hM y hy)
  have key : ∀ g ∈ cent (rat V γ), ∀ y ∈ S, act D.sp.cm V g y ∈ S := by
    intro g hg y hy
    obtain ⟨p, e⟩ := exists_aeval_of_mem_cent hγ hg
    change (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 *ᵥ y ∈ S
    rw [e]
    exact hp p y hy
  exact fun y => ⟨key g hg y, fun hy => by
    have := key g⁻¹ (inv_mem hg) _ hy
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv] at this⟩

theorem exists_ne_zero_mem_sub {D : D7} {V : HSp D} (Φ : WittFrame V) {u : SV (wittIndex V)} (hu : u ≠ 0) :
    ∃ x ∈ Φ.sub u, x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  have h1 := Φ.ef i i
  rw [if_pos rfl] at h1
  rcases h : u i with _ | _ | _
  · exact absurd h hi
  · refine ⟨Φ.f i, Submodule.subset_span (Or.inr ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1
  · refine ⟨Φ.e i, Submodule.subset_span (Or.inl ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1

theorem cent_levi (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (hP : IsPar P) (γ : GF V)
    (hγ : IsRegSS γ.1.1) (hl : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P) :
    IsMulCommutative (cent (rat V γ)) ∧ cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P ∧
      (P ≠ ∅ → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w))) := by
  have hl' : ∀ u ∈ P, rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) ∧
      rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (-u)) := fun u hu =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hl u) hu)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_, fun hne w hK => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval_of_mem_cent hγ a.2
    obtain ⟨q, hq⟩ := exists_aeval_of_mem_cent hγ b.2
    apply GlobalTheory.AdelicU.matHom_injective (AF D.host.F) D.sp.cm.sig V.gram
    apply Units.ext
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, hp, hq]
    rw [← map_mul, ← map_mul, mul_comm]
  · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).1
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).2
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hu0 : u ≠ 0 := fun e => hP.1 (e ▸ hu)
    have := nontrivial_AF D.host.F
    have hi : rat V γ⁻¹ ∈ Φ.levi D.sp.cm (AF D.host.F) P := by rw [map_inv]; exact inv_mem hl
    have hi' := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hi u) hu)
    have h1 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).1
    have h2 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).2
    have h3 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.1
    have h4 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.2
    obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.T.exists_rationalUnitary_scaling_wittFrame D V Φ u
    have hc : Commute g γ := GlobalTheory.T.commute_of_wittFrame_weights D V Φ u γ g 2 h1 h2 h3 h4 g1 g2 g3
    obtain ⟨x, hxu, hx0⟩ := exists_ne_zero_mem_sub Φ hu0
    obtain ⟨n, hn⟩ := GlobalTheory.T.exists_pow_archProj_not_mem_of_eigenvalue_two D V g x hx0 (g1 x hxu) w _ hK
    exact hn (mem_cent.2 (((hc.pow_left n).map (rat V)).map (projArch D.sp.cm.sig V.gram w)).eq)

end GlobalTheory.LeviCent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.centralizer_regular_levi_commutative_noncompact : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) P, IsPar P → ∀ γ : GF V, IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P → IsMulCommutative (cent (rat V γ)) ∧ cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P ∧ (P ≠ ∅ → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w))) := by
  first | exact @GlobalTheory.LeviCent.cent_levi | exact GlobalTheory.LeviCent.cent_levi | (intros; apply GlobalTheory.LeviCent.cent_levi <;> assumption)
end
end
