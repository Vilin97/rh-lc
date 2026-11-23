module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSimplePieces

section

@[expose] public section

noncomputable section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open scoped LaurentSeries PowerSeries

theorem exists_simple_quotient {k G : Type} [Field k] [Group G] (B : Ob k G) (hB : B.m ≠ 0) :
    ∃ (A C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A B f ∧ IsHom B C p ∧ Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p ∧
      IsSimpleModule (MonoidAlgebra k G) C.ρ.asModule ∧ A.m < B.m := by
  haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial
  have hfl := finiteLength_asModule B.ρ
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left
    bot_ne_top
  let S' : Submodule k (Fin B.m → k) := (S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap
  have hinv : ∀ g, S' ≤ S'.comap (B.ρ g) := by
    intro g x hx
    have hx' : B.ρ.asModuleEquiv.symm x ∈ S := hx
    change B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact S.smul_mem _ hx'
  obtain ⟨A, eA, hA⟩ := exists_ob (B.ρ.subrepresentation S' hinv)
  obtain ⟨C, eC, hC⟩ := exists_ob (B.ρ.quotient S' hinv)
  have hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ) := fun g x => hC g (S'.mkQ x)
  have hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ) := eC.surjective.comp S'.mkQ_surjective
  refine ⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp,
    S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩
  · intro g x
    obtain ⟨y, rfl⟩ := eA.surjective x
    rw [← hA]
    simp
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]
    exact ⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩
  · let q := asModuleMap (π := B.ρ) (π' := C.ρ) _ hp
    have hq : Function.Surjective q := hps
    have hk : S = LinearMap.ker q := by
      ext x
      change _ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Iff.rfl
    haveI := isSimpleModule_iff_isCoatom.mpr hS
    exact IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm
  · have h1 : S' ≠ ⊤ := by
      intro h
      refine hS.1 (eq_top_iff.mpr fun x _ => ?_)
      have : B.ρ.asModuleEquiv x ∈ S' := h ▸ Submodule.mem_top
      exact this
    have h2 := Submodule.finrank_lt h1
    rw [eA.finrank_eq] at h2
    simpa using h2

theorem sameSS_piRep_succ {k G : Type} [Field k] [Group G] {s : ℕ} (C : Fin (s + 1) → Ob k G) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin (C 0).m → k))
    (ef : IsHom A B f) (ep : IsHom B (C 0) p) (hf : Function.Injective f) (hp : Function.Surjective p)
    (H : Function.Exact f p) (h : SameSS A.ρ (piRep fun a : Fin s => (C a.succ).ρ)) :
    SameSS B.ρ (piRep fun a => (C a).ρ) := by
  have h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ)) :=
    SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _)
      (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h
      (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩))
  refine h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_
  funext a
  refine Fin.cases ?_ (fun j => ?_) a <;> rfl

theorem ModTh.exists_simple_pieces : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  intro k G _ _ l n _ _ _ R F r Dt M B
  induction B using (measure fun A : Ob k G => A.m).wf.induction with
  | _ B ih =>
  intro N hN
  by_cases hB : B.m = 0
  · haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩
    refine ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩
    · exact SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
        (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      unfold sen qmult gmult
      exact Module.finrank_zero_of_subsingleton
  · obtain ⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩ := exists_simple_quotient B hB
    obtain ⟨s, C, L, hL, hC, hss, hsen⟩ := ih A hlt _ (GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A B f N ef hf hN)
    obtain ⟨hobj, hlat, -, hc⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
    let C' : Fin (s + 1) → Ob k G := Fin.cons C₀ C
    refine ⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_,
      sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact ModTh.model_push_of_surjective F M B C₀ p N ep hp hN
      · exact hL j
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact hs
      · exact hC j
    · rw [Fin.sum_univ_succ, GlobalTheory.T.senMultiplicity_additive_exact_sequence F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]
      rfl

end GlobalTheory.Models
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSimplePiecesStatement

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_simple_pieces_sen_sum : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  first | exact @GlobalTheory.Models.ModTh.exists_simple_pieces | exact GlobalTheory.Models.ModTh.exists_simple_pieces | (intros; apply GlobalTheory.Models.ModTh.exists_simple_pieces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLine

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models.ThroughLine

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (K : Ob k G) (f : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A f ∧ Function.Injective f ∧ Function.Exact f p := by
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) (fun g x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hp g x, LinearMap.mem_ker.mp hx, map_zero]))
  refine ⟨K, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (LinearMap.ker p).subtype_injective.comp e.symm.injective, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [← he]
    simp
  · exact ⟨e ⟨y, hy⟩, by simp⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact j q := by
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨A.ρ g y, hj g y⟩))
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => he g (Submodule.Quotient.mk x),
    e.surjective.comp (LinearMap.range j).mkQ_surjective, fun y => ?_⟩
  simp [Submodule.Quotient.mk_eq_zero]

theorem simple_chr (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have h : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule k (Fin 1 → k)) (congrArg Subrepresentation.toSubmodule h')
  · rcases eq_bot_or_eq_top S.toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.toSubmodule_injective h')
    · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem sameSS_three {s t u : ℕ} {M : Type} [AddCommGroup M] [Module k M] {π : Representation k G M}
    (C : (Fin s ⊕ Unit) ⊕ Fin t → Ob k G) (e : Fin u ≃ (Fin s ⊕ Unit) ⊕ Fin t)
    (h : SameSS π (((piRep fun a => (C (.inl (.inl a))).ρ).prod (C (.inl (.inr ()))).ρ).prod
      (piRep fun a => (C (.inr a)).ρ))) : SameSS π (piRep fun a => (C (e a)).ρ) := by
  have h1 : SameSS π (piRep fun a => (C a).ρ) := by
    refine h.congr_right
      ((((LinearEquiv.refl k _).prodCongr (LinearEquiv.piUnique k (fun a : Unit => Fin (C (.inl (.inr a))).m → k)).symm).trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s) Unit (fun a => Fin (C (.inl a)).m → k)).symm).prodCongr
          (LinearEquiv.refl k _) |>.trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s ⊕ Unit) (Fin t) (fun a => Fin (C a).m → k)).symm) ?_
    intro g x
    funext a
    rcases a with (a | a) | a <;> rfl
  refine h1.congr_right (LinearEquiv.piCongrLeft k (fun a => Fin (C a).m → k) e).symm ?_
  intro g x
  rfl

end GlobalTheory.Models.ThroughLine


open GlobalTheory.Models.ThroughLine in
theorem GlobalTheory.Models.ModTh.exists_jordanHolder_through_line : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  intro k G _ _ l n _ _ _ R F r Dt M B A₁ χ j p N hN hj hji hp hps
  obtain ⟨K, f, hf, hfi, hfe⟩ := exists_ker A₁ (chr χ) p hp
  obtain ⟨Q, q, hq, hqs, hqe⟩ := exists_coker A₁ B j hj
  have hA := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ B j N hj hji hN
  have hK := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M K A₁ f _ hf hfi hA
  have hL := GlobalTheory.Models.ModTh.model_push_of_surjective F M A₁ (chr χ) p _ hp hps hA
  have hQ := GlobalTheory.Models.ModTh.model_push_of_surjective F M B Q q _ hq hqs hN
  obtain ⟨s, C, L, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M K _ hK
  obtain ⟨t, C', L', d1, d2, d3, d4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M Q _ hQ
  obtain ⟨oB, lB, -, cB⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
  obtain ⟨oA, lA, -, cA⟩ := GlobalTheory.T.obj_and_abc_of_model F M A₁ _ hA
  let S : (Fin s ⊕ Unit) ⊕ Fin t → Σ A : Ob k G, Lats k n A.m :=
    Sum.elim (Sum.elim (fun a => ⟨C a, L a⟩) fun _ => ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩)
      fun a => ⟨C' a, L' a⟩
  let e := (Fintype.equivFin ((Fin s ⊕ Unit) ⊕ Fin t)).symm
  have hfl : ∀ m : ℕ, IsFiniteLength k (Fin m → k) := fun m =>
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨_, fun a => (S (e a)).1, fun a => (S (e a)).2, e.symm (.inl (.inr ())), fun a => ?_, fun a => ?_,
    ?_, fun i x => ?_, ?_⟩
  · show M.Model (S (e a)).1 (S (e a)).2
    rcases e a with (b | b) | b
    exacts [c1 b, hL, d1 b]
  · show IsSimpleModule (MonoidAlgebra k G) (S (e a)).1.ρ.asModule
    rcases e a with (b | b) | b
    exacts [c2 b, simple_chr χ, d2 b]
  · refine sameSS_three (fun a => (S a).1) e ?_
    exact (SameSS.of_exact hj hq hji hqs hqe (hfl _)).trans
      (((SameSS.of_exact hf hp hfi hps hfe (hfl _)).trans (c3.prod (SameSS.refl _ (hfl _)))).prod d3)
  · rw [Equiv.sum_comp e (fun a => sen ((F.D (S a).1).γ i) ((S a).2 i) x), Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit),
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B Q j q N oB hj hq hji hqs hqe i (lB i) (cB i) x,
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ (chr χ) f p _ oA hf hp hfi hps hfe i (lA i) (cA i) x, c4, d4]
    rfl
  · show S (e (e.symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJordanHolderThroughLineStatement

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_jordanHolder_through_line_alt : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  first | exact @GlobalTheory.Models.ModTh.exists_jordanHolder_through_line | exact GlobalTheory.Models.ModTh.exists_jordanHolder_through_line | (intros; apply GlobalTheory.Models.ModTh.exists_jordanHolder_through_line <;> assumption)
end
end
