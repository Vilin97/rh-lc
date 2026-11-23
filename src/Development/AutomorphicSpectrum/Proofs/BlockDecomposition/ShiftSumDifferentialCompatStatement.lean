module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescendsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBOfSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomologyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescendsStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomology

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.DsumCoh

variable {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K)

def inj (i : I) : Cx.Hom (E i) (Dsum E) (RingHom.id K) where
  f n := DirectSum.lof K I (fun i => (E i).X n) i
  comm n x := by
    change DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x) = _
    rw [DirectSum.lmap_lof]
    rfl

def prj (i : I) : Cx.Hom (Dsum E) (E i) (RingHom.id K) where
  f n := DirectSum.component K I (fun i => (E i).X n) i
  comm n x := by
    change (E i).d n (DirectSum.component K I (fun i => (E i).X n) i x) =
      DirectSum.component K I (fun i => (E i).X (n + 1)) i (DirectSum.lmap (fun i => (E i).d n) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      by_cases h : j = i
      · subst h
        simp only [DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dite_eq_right h, dite_eq_right h, map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

def toH (n : ℕ) : (⨁ i, (E i).H n) →ₗ[K] (Dsum E).H n :=
  DirectSum.toModule K I _ fun i => (inj E i).mapH n

theorem prj_toH (n : ℕ) (i : I) (y : ⨁ i, (E i).H n) :
    (prj E i).mapH n (toH E n y) = DirectSum.component K I (fun i => (E i).H n) i y := by
  have hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y →
      (E i).cls x hx = (E i).cls y hy := by
    rintro x _ _ _ rfl
    rfl
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j z =>
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
    have h1 : (Dsum E).d n ((inj E j).f n a) = 0 := CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha
    rw [← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1,
      CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) _ h1)]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.component.lof_self]
      exact hcl _ _ _ _ (DirectSum.component.lof_self K _ _)
    · rw [DirectSum.component.of, dite_eq_right hji]
      rw [← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]
      refine hcl _ _ _ _ ?_
      show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0
      rw [DirectSum.component.of, dite_eq_right hji]
  | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]

theorem toH_injective (n : ℕ) : Function.Injective (toH E n) := by
  refine (injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_
  refine DirectSum.ext fun i ↦ ?_
  have h := prj_toH E n i y
  rw [hy, map_zero] at h
  rw [DirectSum.apply_eq_component K, ← h]
  rfl

theorem toH_surjective (n : ℕ) : Function.Surjective (toH E n) := by
  classical
  intro z
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
  have hc : ∀ i, (E i).d n ((prj E i).f n x) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx
  have hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)
  have hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0,
      (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h =
        ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h
    | insert j S hj ih =>
      intro h
      have hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0 := by

        rw [map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ hci i
      simp only [Finset.sum_insert hj]
      rw [CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]
  have hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x := by
    conv_rhs => rw [← DirectSum.sum_support_of x]
    rfl
  refine ⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩

  rw [map_sum]
  simp only [toH, DirectSum.toModule_lof]
  have hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0 := by
    rw [hx_eq]
    exact hx
  rw [Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']
  exact (CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)

end GlobalTheory.CompanionTheory.KunGlue.DsumCoh

theorem GlobalTheory.CompanionTheory.KunGlue.dsum_coh : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ),
    ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0)
      (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0),
      e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) =
        (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  intro K _ I _ E n
  refine ⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩,
    fun i x hx hx' ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]
  exact CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomologyStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.direct_sum_complex_cohomology : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ), ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0) (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0), e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) = (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.dsum_coh | exact GlobalTheory.CompanionTheory.KunGlue.dsum_coh | (intros; apply GlobalTheory.CompanionTheory.KunGlue.dsum_coh <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.MvSum

variable {K : Type} [Field K]

def shIn (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) : (Sh ς k C).X n :=
  show ∀ m' : {m' : ℕ // m' + k = n}, C.X m'.1 from
    fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x

theorem shIn_d (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) (hx : C.d m x = 0) :
    (Sh ς k C).d n (shIn ς C h x) = 0 := by
  funext ⟨m', h'⟩
  cases m' with
  | zero => rfl
  | succ m' =>
    obtain rfl : m' = m := by omega
    change (ς : ℤ) • C.d m' x = 0
    rw [hx, smul_zero]

section Psi

variable {k : ℕ} {C D : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)

def psi (n : ℕ) : (Sh ς k C).X n →ₗ[K] D.X n where
  toFun w := if h : k ≤ n then g (m := n - k) (by omega) (w ⟨n - k, by omega⟩) else 0
  map_add' x y := by
    split_ifs with h
    · exact map_add _ _ _
    · simp
  map_smul' r x := by
    split_ifs with h
    · exact map_smul _ _ _
    · simp

theorem psi_eq {m n : ℕ} (h : m + k = n) (w : (Sh ς k C).X n) : psi ς g n w = g h (w ⟨m, h⟩) := by
  obtain rfl : m = n - k := by omega
  have hk : k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hk]

theorem psi_zero {n : ℕ} (h : n < k) (w : (Sh ς k C).X n) : psi ς g n w = 0 := by
  have hk : ¬ k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hk]

theorem psi_comm
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x))
    (n : ℕ) (w : (Sh ς k C).X n) : D.d n (psi ς g n w) = psi ς g (n + 1) ((Sh ς k C).d n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have h' : m + 1 + k = m + k + 1 := by omega
    rw [psi_eq ς g rfl, psi_eq ς g h', hg rfl h']
    change _ = g h' ((ς : ℤ) • C.d m (w ⟨m, _⟩))
    rw [map_zsmul]
  · rw [psi_zero ς g (by omega), map_zero]
    by_cases h2 : k = n + 1
    · have h0 : 0 + k = n + 1 := by omega
      rw [psi_eq ς g h0]
      change 0 = g h0 0
      rw [map_zero]
    · rw [psi_zero ς g (by omega)]

def shHom
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x)) : Cx.Hom (Sh ς k C) D (RingHom.id K) where
  f n := psi ς g n
  comm n x := psi_comm ς g hg n x

end Psi

theorem psi_nat {k : ℕ} {C C' D D' : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)
    (g' : ∀ {m n : ℕ}, m + k = n → C'.X m →ₗ[K] D'.X n) (f : Cx.Hom C C' (RingHom.id K))
    (f' : Cx.Hom D D' (RingHom.id K))
    (hn : ∀ {m n : ℕ} (h : m + k = n) (x : C.X m), f'.f n (g h x) = g' h (f.f m x))
    (n : ℕ) (w : (Sh ς k C).X n) : psi ς g' n ((Sh.map ς k f).f n w) = f'.f n (psi ς g n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    rw [psi_eq ς g rfl, psi_eq ς g' rfl, hn]
    rfl
  · rw [psi_zero ς g (by omega), psi_zero ς g' (by omega), map_zero]

section Sum

variable {I : Type 1} [DecidableEq I]

def sumHom {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) :
    Cx.Hom (Dsum E) D (RingHom.id K) where
  f n := DirectSum.toModule K I _ fun i => (φ i).f n
  comm n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change D.d n (DirectSum.toModule K I _ (fun i => (φ i).f n) (DirectSum.lof K I (fun i => (E i).X n) i x)) =
        DirectSum.toModule K I _ (fun i => (φ i).f (n + 1))
          (DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x))
      rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof, (φ i).comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sumHom_lof {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) (n : ℕ) (i : I)
    (x : (E i).X n) : (sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x) = (φ i).f n x :=
  DirectSum.toModule_lof _ _ _

theorem sumHom_nat {E E' : I → Cx.{1} K} {D D' : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K))
    (φ' : ∀ i, Cx.Hom (E' i) D' (RingHom.id K)) (a : ∀ i, Cx.Hom (E i) (E' i) (RingHom.id K))
    (b : Cx.Hom D D' (RingHom.id K)) (h : ∀ i n x, (φ' i).f n ((a i).f n x) = b.f n ((φ i).f n x)) (n : ℕ)
    (x : (Dsum E).X n) : (sumHom φ').f n ((Dsum.map a).f n x) = b.f n ((sumHom φ).f n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    have e : (Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x) =
        DirectSum.lof K I (fun i => (E' i).X n) i ((a i).f n x) := DirectSum.lmap_lof _ _ _
    change (sumHom φ').f n ((Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x)) =
      b.f n ((sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x))
    rw [e, sumHom_lof, sumHom_lof, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def eSh (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Classical.choose ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h)

theorem eSh_cls (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n)
    (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0) :
    eSh ς C h (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy :=
  Classical.choose_spec ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h) y hy hy'

variable (k : I → ℕ) (ς : I → ℤˣ) (C : I → Cx.{1} K) (n : ℕ)

abbrev Ix : Type 1 := {v : I × ℕ // v.2 + k v.1 = n}

def reF : (⨁ v : Ix k n, (C v.1.1).H v.1.2) →ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  DirectSum.toModule K _ _ fun v =>
    (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1) ∘ₗ (eSh (ς v.1.1) (C v.1.1) v.2).toLinearMap

def reG : (⨁ u, (Sh (ς u) (k u) (C u)).H n) →ₗ[K] ⨁ v : Ix k n, (C v.1.1).H v.1.2 :=
  DirectSum.toModule K I _ fun u =>
    if h : k u ≤ n then
      (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) ⟨(u, n - k u), by change n - k u + k u = n; omega⟩) ∘ₗ
        (eSh (ς u) (C u) (m := n - k u) (n := n) (by omega)).symm.toLinearMap
    else 0

theorem reG_reF : reG k ς C n ∘ₗ reF k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
  obtain ⟨⟨u, m⟩, h⟩ := v
  have h' : m + k u = n := h
  obtain rfl : m = n - k u := by omega
  have hk : k u ≤ n := by omega
  simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

theorem reF_reG : reF k ς C n ∘ₗ reG k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun y => ?_
  by_cases hk : k u ≤ n
  · simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · have : Subsingleton ((Sh (ς u) (k u) (C u)).H n) := (GlobalTheory.T.shifted_complex_cohomology (ς u) (k u) (C u) n).1 (by omega)
    rw [Subsingleton.elim y 0, map_zero, map_zero]

def reE : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  LinearEquiv.ofLinear (reF k ς C n) (reG k ς C n) (reF_reG k ς C n) (reG_reF k ς C n)

theorem exists_P : ∃ P : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] (Dsum fun u => Sh (ς u) (k u) (C u)).H n,
    ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0),
      P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
        (Dsum fun u => Sh (ς u) (k u) (C u)).cls
          (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) hw := by
  obtain ⟨e1, he1⟩ := GlobalTheory.T.direct_sum_complex_cohomology (fun u => Sh (ς u) (k u) (C u)) n
  refine ⟨(reE k ς C n).trans e1, ?_⟩
  intro v x hx hw
  have hy := shIn_d (ς v.1.1) (C v.1.1) v.2 x hx
  rw [LinearEquiv.trans_apply]
  have h1 : reE k ς C n (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
      DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1
        ((Sh (ς v.1.1) (k v.1.1) (C v.1.1)).cls (shIn (ς v.1.1) (C v.1.1) v.2 x) hy) := by
    change reF k ς C n _ = _
    rw [reF, DirectSum.toModule_lof]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← eSh_cls (ς v.1.1) (C v.1.1) v.2 _ hy hx]
    rfl
  rw [h1]
  exact he1 v.1.1 _ hy hw

variable {D : Cx.{1} K} (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (C u).X m →ₗ[K] D.X n)
  (hg : ∀ (u : I) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : (C u).X m),
    D.d n (g u h x) = (ς u : ℤ) • g u h' ((C u).d m x))

include hg in
theorem g_cocycle (u : I) {m n : ℕ} (h : m + k u = n) (x : (C u).X m) (hx : (C u).d m x = 0) :
    D.d n (g u h x) = 0 := by
  rw [hg u h (by omega), hx, map_zero, smul_zero]

theorem bij_iff : Function.Bijective ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ↔
    ∃ e : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] D.H n,
      ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
        (hz : D.d n (g v.1.1 v.2 x) = 0),
        e (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
          D.cls (g v.1.1 v.2 x) hz := by
  obtain ⟨P, hP⟩ := exists_P k ς C n
  have key : ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hz : D.d n (g v.1.1 v.2 x) = 0),
      (sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n
        (P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx))) =
        D.cls (g v.1.1 v.2 x) hz := by
    intro v x hx hz
    have hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0 := by
      change DirectSum.lmap _ _ = 0
      rw [DirectSum.lmap_lof, shIn_d _ _ _ _ hx, map_zero]
    have hf : (sumHom fun u => shHom (ς u) (g u) (hg u)).f n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) =
        g v.1.1 v.2 x := by
      rw [sumHom_lof]
      exact psi_eq (ς v.1.1) (g v.1.1) v.2 _
    rw [hP v x hx hw, CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (by rw [hf]; exact hz)]
    exact GlobalTheory.CompanionTheory.ConeKillC.cls_congr _ hf _ _
  constructor
  · intro hb
    refine ⟨P.trans (LinearEquiv.ofBijective _ hb), fun v x hx hz => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
    exact key v x hx hz
  · rintro ⟨e, he⟩
    have hEq : ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ₗ P.toLinearMap = e.toLinearMap := by
      refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.CompanionTheory.ConeKillC.cls_surj _ _ y
      have hz := g_cocycle k ς C g hg v.1.1 v.2 x hx
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [key v x hx hz, he v x hx hz]
    have hb : Function.Bijective (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) := by
      have : (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) = e := by
        funext y
        exact LinearMap.congr_fun hEq y
      rw [this]
      exact e.bijective
    exact (Function.Bijective.of_comp_iff _ P.bijective).1 hb

end Sum

variable {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def mvHom (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι)
    (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n)
    (hd : ∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m),
      (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x))
    (hn : ∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m),
      (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) :
    (sumSy fun u => shSy (ς u) (k u) (A u)).Hom T where
  φ S := sumHom (E := fun u => Sh (ς u) (k u) ((A u).K S)) fun u => shHom (ς u) (g u S) (hd u S)
  nat {S S'} h n x :=
    sumHom_nat (E := fun u => Sh (ς u) (k u) ((A u).K S)) (E' := fun u => Sh (ς u) (k u) ((A u).K S'))
      (fun u => shHom (ς u) (g u S) (hd u S)) (fun u => shHom (ς u) (g u S') (hd u S'))
      (fun u => Sh.map (ς u) (k u) ((A u).res h)) (T.res h)
      (fun u n x => psi_nat (ς u) (g u S) (g u S') ((A u).res h) (T.res h) (fun h' x => hn u h h' x) n x) n x

theorem mvSum : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  intro hMV K _ ι _ _ I _ k ς A T g hd hn hA hT hE n
  have hiff : ∀ (S : Finset ι) (n : ℕ), Function.Bijective (((mvHom k ς A T g hd hn).φ S).mapH n) ↔ MvE k A T g S n :=
    fun S n => bij_iff k ς (fun u => (A u).K S) n (fun u => g u S) (fun u => hd u S)
  exact (hiff ∅ n).1 (hMV K ι _ T (mvHom k ς A T g hd hn)
    (GlobalTheory.T.direct_sum_system_descends _ fun u => GlobalTheory.T.shifted_system_descends _ _ _ (hA u)) hT (fun S hS n => (hiff S n).2 (hE S hS n)) n)

end GlobalTheory.CompanionTheory.KunGlue.MvSum
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompatStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.mvE_empty_of_mvE_nonempty : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | exact GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | (intros; apply GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum <;> assumption)
end
end
