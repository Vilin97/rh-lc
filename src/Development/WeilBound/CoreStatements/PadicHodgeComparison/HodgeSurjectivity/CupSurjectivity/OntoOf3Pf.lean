module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SumCoordBasisDual
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import GroundTheory.PAdicHodge.NormalizedTraceTower
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.RhsF
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.StepA

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem stepA (hC : CupLaws) (P : HTPre l K) {M : Model l K} {d : ℕ} (S : Sq M (d + 1)) (hEt : Etale S.D.f)
    (r : E.Roots l) (v : S.Y.T 2) (hv : IsEtaleFirstChernUntwisted r S.D v) (e : Hdg S.Y.q 1 2) (he : IsDlogFirstChernClass S.Y.q (genD S.D) e)
    (c : S.P.T (2 + 2 * d)) (w : S.Y.T (2 * d)) (z : S.Y.T (2 + 2 * d)) (hz : S.Y.CupT v w z)
    (hcz : S.Y.toV _ (Model.pullT S.π S.hπ _ c) = S.Y.toV _ z) (A : ℕ) (Θ : Module.Dual K (Hdg S.P.q A (2 + 2 * d)))
    (hΘ : ∀ C, (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = A)
      (hn : 2 + n₀ = 2 + 2 * d) (w : Hdg S.Y.q a₀ n₀),
        pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = cupH S.Y.q ha hn e w) → Θ C = 0) :
    P.h S.P A (2 + 2 * d) (S.P.toV _ c) Θ = 0 := by
  obtain ⟨φ, hφf, hφg⟩ : ∃ φ : Module.Dual K (Hdg S.Y.q A (2 + 2 * d)),
      φ ∘ₗ pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A (2 + 2 * d) = Θ ∧
      ∀ (a₀ : ℕ) (ha : 1 + a₀ = A) (u : Hdg S.Y.q a₀ (2 * d)), φ (cupH S.Y.q ha rfl e u) = 0 := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · subst hA
      obtain ⟨φ, h1, -⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) 0 (2 + 2 * d))
        (0 : Hdg S.Y.q 0 (2 + 2 * d) →ₗ[K] Hdg S.Y.q 0 (2 + 2 * d)) Θ
        (fun C u h => hΘ C (Or.inl (by simpa using h)))
      exact ⟨φ, h1, fun a₀ ha => absurd ha (by omega)⟩
    · obtain ⟨a, rfl⟩ : ∃ a, A = 1 + a := ⟨A - 1, by omega⟩
      obtain ⟨φ, h1, h2⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) (1 + a) (2 + 2 * d))
        (cupL hC S.Y.q (a := 1) (a' := a) (c := 1 + a) (i := 2) (j := 2 * d) (n := 2 + 2 * d) rfl rfl e) Θ
        (fun C u h => hΘ C (Or.inr ⟨a, 2 * d, rfl, rfl, u, by rw [h, cupL_apply]⟩))
      refine ⟨φ, h1, fun a₀ ha u => ?_⟩
      obtain rfl : a₀ = a := by omega
      have := LinearMap.congr_fun h2 u
      simpa [cupL_apply] using this
  have hc1 := P.c1 S.Y S.smY S.D hEt S.loc r v e hv he
  let b : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a 2))) K (Hdg S.Y.q a 2) := fun a =>
    haveI := (P.fin S.Y S.smY a 2).1
    Module.finBasis K _
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a (2 * d)))) K (Hdg S.Y.q a (2 * d)) := fun a =>
    haveI := (P.fin S.Y S.smY a (2 * d)).1
    Module.finBasis K _
  have key : ∀ (a a' : ℕ) (ha : a + a' = A), ∑ s, ∑ s', P.h S.Y a 2 (S.Y.toV _ v) ((b a).coord s) *
      P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
        kC K (φ (cupH S.Y.q ha rfl (b a s) (b' a' s'))) = 0 := by
    intro a a' ha
    by_cases h1 : a = 1
    · subst h1
      simp_rw [hc1.1]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s' _ => ?_
      have hs := esum (kC K) (b 1) (φ ∘ₗ (cupL hC S.Y.q (i := 2) (j := 2 * d) ha rfl).flip (b' a' s')) e
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply] at hs
      rw [hφg a' ha, map_zero] at hs
      calc ∑ s, kC K ((b 1).coord s e) * P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s')))
          = P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            ∑ s, kC K ((b 1).coord s e) * kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s'))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ = 0 := by rw [hs, mul_zero]
    · refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
      rw [hc1.2 a h1, zero_mul, zero_mul]
  rw [← hφf, ← P.nat S.Y S.P S.π S.hπ S.smY S.smP A (2 + 2 * d) (S.P.toV _ c) φ, pullV_toV, hcz,
    P.cup S.Y S.smY v w z hz b b' A φ]
  exact Finset.sum_eq_zero fun p _ => key _ _ _

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.MkDat

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem mkDat (hC : CupLaws) (hK : HodgeKill) (hD : DiagEt3) (P : HTPre l K) [FiniteDimensional ℚ_[l] K] {M : Model l K}
    {d : ℕ} (hd : 1 ≤ d) (hM : M.Sm) (hs : SmoothOfRelativeDimension (d + 1) M.p) (S : Sq M (d + 1)) (hEt : Etale S.D.f) :
    Nonempty (Dat hC P M d) := by
  obtain ⟨r⟩ := GlobalTheory.CompanionTheory.RootsC.rootsEx l
  obtain ⟨v, hv⟩ := (P.first_chern_class_exists S.Y S.smY S.D hEt S.loc).1 r
  obtain ⟨e, he, -⟩ := (P.first_chern_class_exists S.Y S.smY S.D hEt S.loc).2
  obtain ⟨c, w, z, m₀, a₀, b₀, ab₀, m, i, j, hij, a, b, ab, one, N, hz, hcz, hcup₀, hcup, hjne, hdec, hone, hN, hli,
    hsum₀⟩ := hD l K M d hd hM hs S hEt r v hv
  have := (sm_gen S.smP).1
  have := (sm_gen S.smP).2
  have := proper_genMap S.π S.hπ S.smY S.smP
  refine ⟨⟨S, c, m₀, a₀, b₀, ab₀, m, i, j, hij, a, b, ab, one, N, hcup₀, hcup, hjne, hdec, hone, hN, hli, hsum₀, ?_⟩⟩
  intro A a' n' y hy Θ
  apply stepA hC P S hEt r v hv e he c w z hz hcz A
  intro C hCd
  rw [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply,
    killR hK (↥K) M.gen S.P.gen S.Y.gen S.P.q (Model.genMap S.Δ S.hΔ) (Model.genMap S.π S.hπ) S.Y.q
      (Model.genMap_q S.π S.hπ) M.q (Model.genMap_q S.Δ S.hΔ) (genD S.D) (d + 1) (by omega) S.blow e he A (2 + 2 * d)
      a' n' C y hCd hy, map_zero]

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SurjOfCore

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem surj_of_core (hC : CupLaws) (P : HTPre l K) (M : Model l K) (n : ℕ)
    (h : ∀ a' (x : Hdg M.q a' n), ∃ N : ℚ_[l], N ≠ 0 ∧ tgt hC x N ∈ Sp P M n) : Surj P M n := by
  intro m b z hz a' ha'
  funext s0
  let L : GF M n →ₗ[ℂ_[l]] ℂ_[l] :=
    { toFun := fun g => ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * g a ((b a).coord s)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        ring }
  have hL : Sp P M n ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hz v
  obtain ⟨N, hN, hmem⟩ := h a' (b a' s0)
  have h0 : L (tgt hC (b a' s0) N) = 0 := hL hmem
  have hGe : ∀ s, Gx hC (b a' s0) ((b a').coord s) (oneH M.q) = (b a').coord s (b a' s0) := by
    intro s
    unfold Gx
    rw [dite_eq_left (Nat.zero_add a')]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC _ _ M.q).2.2.2.1]
  have hGn : ∀ a, a ≠ a' → ∀ s, Gx hC (b a' s0) ((b a).coord s) (oneH M.q) = 0 := by
    intro a ha s
    unfold Gx
    rw [dite_eq_right (by omega)]
    rfl
  have hv : L (tgt hC (b a' s0) N) = z a' s0 * qC l N := by
    show ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * (qC l N * kC K (Gx hC (b a' s0) ((b a).coord s) (oneH M.q))) = _
    rw [Finset.sum_eq_single a']
    · simp only [hGe, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single s0]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hGn a ha]
      simp
    · intro ha
      exact absurd (Finset.mem_range.2 (by omega)) ha
  rw [hv] at h0
  have hq : qC l N ≠ 0 := (map_ne_zero (qC l)).2 hN
  simpa [hq] using h0

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Tgt

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem core (hC : CupLaws) (hS : Slant) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (Dt : Dat hC P M d)
    (hfin : FiniteDimensional ℚ_[l] (M.V (2 + 2 * d))) (hI : P.Inj M (2 + 2 * d)) {a' n : ℕ} (x : Hdg M.q a' n) :
    tgt hC x Dt.N ∈ Sp P M n := by
  classical
  have hR : ∀ (α : ℕ) (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))), rhsF hC P Dt x φ' ∈ Sp P M n := by
    intro α φ'
    rw [← eid hC hS P hM Dt x φ']
    unfold lhsF Sp
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun s _ => ?_) (Submodule.sum_mem _ fun s _ => ?_) <;>
      split_ifs <;>
      first
        | exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
        | exact Submodule.zero_mem _
  have hsum : ∀ G : Module.Dual K (Hdg M.q 0 0),
      ∑ s, P.h M 0 0 (M.toV 0 (Dt.b₀ s)) G = qC l Dt.N * kC K (G (oneH M.q)) := by
    intro G
    have e1 : ∑ s, P.h M 0 0 (M.toV 0 (Dt.b₀ s)) G = P.h M 0 0 (∑ s, M.toV 0 (Dt.b₀ s)) G := by

      rw [map_sum, AddMonoidHom.finsetSum_apply]
    rw [e1, Dt.sum₀, P.lin, P.one M hM Dt.one Dt.hone]
  let vec : (Σ α : ℕ, Module.Dual K (Hdg M.q α (2 + 2 * d))) → (Fin Dt.m₀ → ℂ_[l]) :=
    fun p s => P.h M p.1 (2 + 2 * d) (M.toV _ (Dt.a₀ s)) p.2
  have h1 : (fun _ => (1 : ℂ_[l])) ∈ Submodule.span ℂ_[l] (Set.range vec) := by
    by_contra hn
    obtain ⟨f, hf1, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have hvan : ∀ p, f (vec p) = 0 := fun p => by
      have hm : f (vec p) ∈ (Submodule.span ℂ_[l] (Set.range vec)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨p, rfl⟩)
      rw [hf0] at hm
      exact (Submodule.mem_bot _).mp hm
    let z : Fin Dt.m₀ → ℂ_[l] := fun s => f (fun j => if s = j then 1 else 0)
    have hfz : ∀ y, f y = ∑ s, y s * z s := fun y => by
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      simp only [smul_eq_mul, z]
    obtain ⟨S, _, b0, hb0⟩ : ∃ (S : Set (M.V (2 + 2 * d))) (_ : Fintype S)
        (b0 : Module.Basis (Fin Dt.m₀ ⊕ S) ℚ_[l] (M.V (2 + 2 * d))),
        ∀ s, b0 (Sum.inl s) = M.toV _ (Dt.a₀ s) := by
      have hfi := Module.Finite.finite_basis (Module.Basis.sumExtend Dt.li)
      refine ⟨Module.Basis.sumExtendIndex Dt.li, ?_, Module.Basis.sumExtend Dt.li, fun s => ?_⟩
      · exact @Fintype.ofFinite _ (@Finite.of_injective _ _ hfi Sum.inr Sum.inr_injective)
      · simp only [Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend]
        rfl
    let e := Fintype.equivFin (Fin Dt.m₀ ⊕ S)
    let b := b0.reindex e
    let z' : Fin (Fintype.card (Fin Dt.m₀ ⊕ S)) → ℂ_[l] := fun i => Sum.elim z (fun _ => 0) (e.symm i)
    have hyp : ∀ (a : ℕ) (φ : Module.Dual K (Hdg M.q a (2 + 2 * d))),
        ∑ i, z' i * P.h M a (2 + 2 * d) (b i) φ = 0 := by
      intro a φ
      have hv := hvan ⟨a, φ⟩
      rw [hfz] at hv
      simp only [b, z', Module.Basis.reindex_apply]
      rw [Equiv.sum_comp e.symm (fun j => Sum.elim z (fun _ => 0) j * P.h M a (2 + 2 * d) (b0 j) φ),
        Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, hb0]
      refine Eq.trans ?_ hv
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
    have hz' : z' = 0 := hI b z' hyp
    have hz : z = 0 := by
      funext s
      have hs := congrFun hz' (e (Sum.inl s))
      simpa [z'] using hs
    apply hf1
    rw [hfz]
    simp [hz]
  let Φ : (Fin Dt.m₀ → ℂ_[l]) →ₗ[ℂ_[l]] GF M n :=
    { toFun := fun c β ψ => ∑ s, c s * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ)
      map_add' := fun c c' => by
        funext β ψ
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext β ψ
        simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℂ_[l] (Set.range vec) ≤ (Sp P M n).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hR p.1 p.2
  have hmem := hle h1
  rw [Submodule.mem_comap] at hmem
  convert hmem using 1
  funext β ψ
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  unfold tgt
  exact (hsum _).symm

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoOf3Pf

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ontoOf3_pf : OntoOf3 := by
  intro hC hS hK hSq hD hF l _ K _ P M d hd hM hs hI n
  obtain ⟨S, hEt⟩ := hSq l K M d hd hM hs
  obtain ⟨Dt⟩ := mkDat hC hK hD P hd hM hs S hEt
  exact surj_of_core hC P M n fun a' x => ⟨Dt.N, Dt.hN, core hC hS P hM Dt (hF l K M hM _) hI x⟩

end CrystallineSemistableComparison.Onto

end
end
end
