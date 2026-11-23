module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultEqZeroOfInj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientMultiplicityShiftLatticeQuotient

section

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam.QuotShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section lin
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem mem_iSup_comap_pow (S : Module.End k U) (Q : Submodule k U) (hQ : ∀ q ∈ Q, S q ∈ Q) (p : U) :
    p ∈ ⨆ m : ℕ, Q.comap (S ^ m) ↔ ∃ m : ℕ, (S ^ m) p ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact hQ _ hy
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem gmult_transport (T T' : Module.End k U) (e : U ≃ₗ[k] U) (P Q P' Q' : Submodule k U)
    (hP' : ∀ p, e p ∈ P' ↔ p ∈ P) (hQ' : ∀ p, e p ∈ Q' ↔ p ∈ Q)
    (hTP : ∀ p ∈ P, T p ∈ P) (hTQ : ∀ p ∈ Q, T p ∈ Q) (hTQ' : ∀ p ∈ Q', T' p ∈ Q') (x y : k)
    (h : ∀ p ∈ P, (T' (e p) - x • e p) - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  set S := T - algebraMap k (Module.End k U) y with hS
  set S' := T' - algebraMap k (Module.End k U) x with hS'
  have hSa : ∀ p, S p = T p - y • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have hSa' : ∀ p, S' p = T' p - x • p := fun p => by simp [hS', Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hSa']; exact Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)
  have key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro p hp m
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ ih.1, ?_⟩
      have h1 := hSQ' _ ih.2
      have h2 := h _ ih.1
      rw [← hSa, ← hSa'] at h2
      have h3 := Q'.add_mem h1 h2
      rwa [map_sub, sub_add_sub_cancel] at h3
  have hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) := by
    intro p
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']
    refine and_congr_right fun hp => exists_congr fun m => ?_
    rw [← hQ']
    have := (key p hp m).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 this
    · intro h1; simpa using Q'.add_mem this h1
  unfold gmult
  rw [← hS, ← hS']
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)
  have hA : A.map (e : U →ₗ[k] U) = A' := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem]
    exact Submodule.map_equiv_eq_comap_symm e A ▸ by simp
  let e' : A ≃ₗ[k] A' := e.ofSubmodules A A' hA
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm
  ext z
  obtain ⟨w, rfl⟩ := e'.surjective z
  have : (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A := hQ' w
  rw [this]
  exact Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp

theorem fin_of_le {A B C : Submodule k U} (h : C ≤ B) (hf : FiniteDimensional k (A.map C.mkQ)) :
    FiniteDimensional k (A.map B.mkQ) := by
  have : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [this]; infer_instance

theorem fin_trans {A B C : Submodule k U} (h : C ≤ B) (h1 : FiniteDimensional k (A.map B.mkQ))
    (h2 : FiniteDimensional k (B.map C.mkQ)) : FiniteDimensional k (A.map C.mkQ) := by
  have e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h1
  have hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ := by
    rintro _ ⟨⟨a, -, rfl⟩, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩
  have h3 := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h)
    (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))

theorem fin_quot {A B : Submodule k U} (h : FiniteDimensional k (A.map B.mkQ)) :
    FiniteDimensional k (↥A ⧸ B.submoduleOf A) := by
  have e := LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at e
  exact e.symm.finiteDimensional

theorem gmult_self (T : Module.End k U) (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  rw [Submodule.submoduleOf_eq_top.2 inf_le_left]
  exact Module.finrank_zero_of_subsingleton

end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_sup_le {P Q : Submodule k⟦X⟧ V} {m : ℕ} (h : sh ((m + 1 : ℕ) : ℤ) P ≤ Q) :
    sh (m : ℤ) (Q ⊔ sh 1 P) ≤ Q := by
  have : sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P) := Submodule.map_sup _ _ _
  rw [this, sh_sh_eq]
  refine sup_le ?_ (by exact_mod_cast h)
  simpa [sh_zero_eq] using sh_le_sh_of_le (Int.natCast_nonneg m) Q

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (P : Submodule k⟦X⟧ V) : sh 1 P ≤ P := by
  simpa [sh_zero_eq] using sh_le_sh_of_le (zero_le_one' ℤ) P

theorem fin_lat (m : ℕ) : ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → sh (m : ℤ) P ≤ Q →
    FiniteDimensional k ((P.restrictScalars k).map (Q.restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    intro P Q _ _ h
    have : (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥ := by
      rw [← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      rw [Nat.cast_zero, sh_zero_eq] at h
      exact h
    rw [this]; infer_instance
  | succ m ih =>
    intro P Q hP hQ h
    refine fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_
      (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))
    exact fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)

theorem step {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {P Q : Submodule k⟦X⟧ V}
    (hP : CondC g P) (hQ : CondC g Q) (h : sh 1 P ≤ Q) (x : k) :
    qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  have hv := vv_ne_zero k
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k
  have he : ∀ p, e p = vv k • p := fun p => rfl
  have hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k := by
    intro N p
    rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul,
      zpow_neg_one, inv_mul_cancel₀ hv, one_smul]
  refine gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp)
    (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_
  obtain ⟨n', hn', hs⟩ := Window.nab_shift R hg hP 1 hp
  rw [zpow_one, ← he, ← he] at hs
  rw [hs, ← map_smul, ← map_sub, ← map_sub, hN]
  have : nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n' := by
    rw [Int.cast_one, add_smul]; abel
  rw [this]
  exact h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)

theorem qmult_add (g : V →ₗ[k] V) (m : ℕ) {P Q S : Submodule k⟦X⟧ V} (hP : P.FG) (hS : S.FG) (h1 : S ≤ Q)
    (h2 : Q ≤ P) (cP : ∀ p ∈ P, nab g p ∈ P) (cQ : ∀ p ∈ Q, nab g p ∈ Q) (cS : ∀ p ∈ S, nab g p ∈ S)
    (h : sh (m : ℤ) P ≤ S) (x : k) : qmult g P S x = qmult g P Q x + qmult g Q S x :=
  GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS
    (fin_quot (fin_lat m P S hP hS h)) x

theorem shift_of_le {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) (x : k) (m : ℕ) :
    ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → Q ≤ P → CondC g P → CondC g Q → sh (m : ℤ) P ≤ Q →
      qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  induction m with
  | zero =>
    intro P Q _ _ hle _ _ h
    rw [Nat.cast_zero, sh_zero_eq] at h
    rw [le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]
  | succ m ih =>
    intro P Q hP hQ hle cP cQ h
    have hle' : Q ⊔ sh 1 P ≤ P := sup_le hle (sh_one_le P)
    have cQ' : CondC g (Q ⊔ sh 1 P) := by
      rw [condC_iff_nab_mem]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)
    have h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q := by
      rw [sh_sh_eq, add_comm, ← sh_sh_eq]; exact sh_le_sh 1 h
    have a1 := qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp)
      (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)
    have a2 := qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _)
      (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp)
      (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x
    rw [a1, a2, step R hg cP cQ' le_sup_right,
      ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x
  obtain ⟨m, hm⟩ := Close.exists_pow hP.1 hQ.2
  exact shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)

end GlobalTheory.PhiGam.QuotShift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientMultiplicityShiftLatticeQuotientStatement

section

@[expose] public section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  first | exact @GlobalTheory.PhiGam.QuotShift.main | exact GlobalTheory.PhiGam.QuotShift.main | (intros; apply GlobalTheory.PhiGam.QuotShift.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelation

section

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam.Count
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

theorem exists_le_sup (P Q : Submodule k U) [FiniteDimensional k (P.map Q.mkQ)] :
    ∃ F : Submodule k U, FiniteDimensional k F ∧ P ≤ F ⊔ Q := by
  obtain ⟨σ, hσ⟩ := Q.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ Q)
  refine ⟨(P.map Q.mkQ).map σ, inferInstance, fun p hp => ?_⟩
  refine Submodule.mem_sup.2 ⟨σ (Q.mkQ p), ⟨_, ⟨p, hp, rfl⟩, rfl⟩, p - σ (Q.mkQ p), ?_, by abel⟩
  have h : Q.mkQ (σ (Q.mkQ p)) = Q.mkQ p := LinearMap.congr_fun hσ _
  exact (Submodule.Quotient.eq _).mp h.symm

theorem finite_of_le_sup {P Q F : Submodule k U} [FiniteDimensional k F] (h : P ≤ F ⊔ Q) :
    FiniteDimensional k (↥P ⧸ Q.submoduleOf P) := by
  have hker : LinearMap.ker (Q.mkQ ∘ₗ P.subtype) = Q.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hle : LinearMap.range (Q.mkQ ∘ₗ P.subtype) ≤ F.map Q.mkQ := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨f, hf, q, hq, rfl⟩ := Submodule.mem_sup.1 (h hp)
    refine ⟨f, hf, ?_⟩
    change Q.mkQ f = Q.mkQ (f + q)
    rw [map_add (f := _), show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hq, add_zero]
  haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P.subtype)) :=
    Submodule.finiteDimensional_of_le hle
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_eq_zero (T : Module.End k U) {P Q M : Submodule k U} (hPM : P ≤ M) (hM : ∀ p ∈ M, T p ∈ M)
    (x : k) (h : ∀ p ∈ M, T p - x • p ∈ Q → p ∈ Q) (hQ : ∀ p ∈ Q, T p ∈ Q) : gmult T P Q x = 0 := by
  set S : Module.End k U := T - algebraMap k (Module.End k U) x with hS
  have hSa : ∀ p, S p = T p - x • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have key : ∀ m : ℕ, ∀ p ∈ M, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      have h1 : S p ∈ M := by rw [hSa]; exact M.sub_mem (hM p hp) (M.smul_mem _ hp)
      exact h p hp (hSa p ▸ ih _ h1 hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply, hSa]
    exact Q.sub_mem (hQ _ hp) (Q.smul_mem _ hp)
  have hle : P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) ≤ Q := by
    rintro p ⟨hp, hq⟩
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hq
    exact key m p (hPM hp) hm
  unfold gmult
  rw [← hS, Submodule.submoduleOf_eq_top.2 hle]
  exact Module.finrank_zero_of_subsingleton

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem exists_le_sup_sh {N : Submodule k⟦X⟧ V} (hN : IsLat N) (m : ℕ) :
    ∃ F : Submodule k V, FiniteDimensional k F ∧
      N.restrictScalars k ≤ F ⊔ (sh m N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp [sh_zero_eq]⟩
  | succ m ih =>
    obtain ⟨F, hF, h⟩ := ih
    haveI := Window.finite_quot (hN.shift m).1
    obtain ⟨F', hF', h'⟩ := exists_le_sup ((sh m N).restrictScalars k) ((sh 1 (sh m N)).restrictScalars k)
    rw [sh_sh_eq, add_comm] at h'
    refine ⟨F ⊔ F', inferInstance, h.trans ?_⟩
    rw [sup_assoc, Nat.cast_succ]
    exact sup_le_sup_left h' _

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (x : k) (h : sen g N (x + b) = 0) :
    ∀ y ∈ sh b N, nab g y - x • y ∈ sh (b + 1) N → y ∈ sh (b + 1) N := by
  apply GlobalTheory.PhiGam.Compare.graded_inj <;> assumption

theorem window_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (x : k) (s : ℕ) (h : ∀ j : ℕ, 1 ≤ j → j ≤ s → sen g N (x - j) = 0) :
    ∀ y ∈ sh (-s) N, nab g y - x • y ∈ N → y ∈ N := by
  induction s with
  | zero => intro y hy _; simpa [sh_zero_eq] using hy
  | succ s ih =>
    intro y hy hy'
    refine ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2)) y ?_ hy'
    have e : (-((s + 1 : ℕ) : ℤ)) + 1 = -(s : ℤ) := by push_cast; ring
    have := graded_inj R hg hN hC (-((s + 1 : ℕ) : ℤ)) x (by
      rw [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]; exact h _ (Nat.succ_pos s) le_rfl) y hy
    rw [e] at this
    refine this (sh_le_sh_of_le (a := 0) (by omega) N ?_)
    rwa [sh_zero_eq]

theorem sen_count : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hQP cP cQ s hs x
  constructor
  · have h1 : ∀ N : Submodule k⟦X⟧ V, sh 1 N ≤ N := fun N => by
      have := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) N
      rwa [sh_zero_eq] at this
    obtain ⟨F, hF, hle⟩ := exists_le_sup_sh hP (s + 1)
    have h2 : sh ((s + 1 : ℕ) : ℤ) P ≤ sh 1 Q := by
      have := sh_le_sh ((s + 1 : ℕ) : ℤ) hs
      rwa [sh_sh_eq, show ((s + 1 : ℕ) : ℤ) + -(s : ℤ) = 1 by push_cast; ring] at this
    have hfin : FiniteDimensional k (↥(P.restrictScalars k) ⧸
        ((sh 1 Q).restrictScalars k).submoduleOf (P.restrictScalars k)) :=
      finite_of_le_sup (F := F) (hle.trans (sup_le_sup_left (fun _ hy => h2 hy) _))
    have a1 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) ((sh 1 P).restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => sh_le_sh 1 hQP hy) (fun _ hy => h1 P hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem_sh R hg cP 1 hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    have a2 := GlobalTheory.PhiGam.GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k)
      ((sh 1 Q).restrictScalars k) (fun _ hy => h1 Q hy) (fun _ hy => hQP hy)
      (fun _ hy => Window.nab_mem cP hy) (fun _ hy => Window.nab_mem cQ hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ 1 hy) hfin x
    rw [← GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient R g hg P Q hP hQ hQP cP cQ x]
    unfold sen qmult
    omega
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (gmult_eq_zero (nab g) (M := (sh (-s) Q).restrictScalars k) (fun _ hy => hs hy)
      (fun _ hy => Window.nab_mem_sh R hg cQ _ hy) x (window_inj R hg hQ.1 cQ x s hno)
      (fun _ hy => Window.nab_mem cQ hy))

end GlobalTheory.PhiGam.Count
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelationStatement

section

@[expose] public section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senMultiplicity_lattice_count_relation : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  first | exact @GlobalTheory.PhiGam.Count.sen_count | exact GlobalTheory.PhiGam.Count.sen_count | (intros; apply GlobalTheory.PhiGam.Count.sen_count <;> assumption)
end
end
