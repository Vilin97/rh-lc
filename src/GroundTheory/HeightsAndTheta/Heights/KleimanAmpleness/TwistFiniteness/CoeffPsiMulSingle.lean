module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.Graded
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.IsUnitPhiOfMemMonos

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

theorem isUnit_phi_of_mem_monos {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0)
    {s : Poly (Sy S r) N} (hs : s ∈ monos I) : IsUnit (phi x η S s) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [phi_X]
    refine isUnit_iff_exists_inv.mpr ⟨single ((-1 : ℤ), (0 : ℤ)) (x i)⁻¹, ?_⟩
    rw [single_mul_single, mul_inv_cancel₀ (hI i (Finset.mem_coe.mp hi)), AddMonoidAlgebra.one_def]
    simp only [Prod.mk_add_mk, add_neg_cancel, add_zero]
    rfl
  | one => rw [map_one]; exact isUnit_one
  | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul hb

theorem isUnit_end {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0) (s : monos (S := Sy S r) I) :
    IsUnit (algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) s) := by
  rw [Module.End.isUnit_iff]
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  constructor
  · intro a b hab
    simp only [Module.algebraMap_end_apply] at hab
    have h1 : phi x η S s * toA x η a = phi x η S s * toA x η b := by
      rw [← toA_smulP, ← toA_smulP, hab]
    rw [← hu] at h1
    exact (toA x η).injective ((Units.mul_right_inj u).mp h1)
  · intro b
    refine ⟨(toA x η).symm (↑u⁻¹ * toA x η b), ?_⟩
    simp only [Module.algebraMap_end_apply]
    apply (toA x η).injective
    rw [toA_smulP, AddEquiv.apply_symm_apply, ← hu, Units.mul_inv_cancel_left]

def locL (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    LocMod (Sy S r) N (TMod x η S n0 d0 g0) I →ₗ[Poly (Sy S r) N] Amb x η :=
  LocalizedModule.lift _ (TMod x η S n0 d0 g0).subtype (isUnit_end x η S hI)

theorem locL_mk (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
      (((isUnit_end x η S hI s).unit⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) :
        Module.End (Poly (Sy S r) N) (Amb x η)) (m : Amb x η) :=
  rfl

theorem phi_mul_locL_mk (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) :
    phi x η S s * toA x η (locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0))) =
      toA x η m := by
  rw [← toA_smulP]
  congr 1
  rw [locL_mk]
  set e := (isUnit_end x η S hI s).unit
  have hspec : (e : Module.End (Poly (Sy S r) N) (Amb x η)) =
      algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) (s : Poly (Sy S r) N) :=
    IsUnit.unit_spec _
  have h1 : (e : Module.End (Poly (Sy S r) N) (Amb x η))
      (((e⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) : Module.End (Poly (Sy S r) N) (Amb x η))
        (m : Amb x η)) = (m : Amb x η) := by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  rw [hspec, Module.algebraMap_end_apply] at h1
  exact h1

theorem locL_mk_eq (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) (a : Amb x η) (ha : phi x η S s * toA x η a = toA x η m) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = a := by
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  apply (toA x η).injective
  have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
  rw [← ha, ← hu] at h1
  exact (Units.mul_right_inj u).mp h1

theorem locL_injective (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    Function.Injective (locL x η S n0 d0 g0 I hI) := by
  intro a b hab
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
      have h2 := phi_mul_locL_mk x η S n0 d0 g0 I hI m' s'
      simp only [Submonoid.smul_def, one_smul]
      apply Subtype.ext
      apply (toA x η).injective
      rw [Submodule.coe_smul, Submodule.coe_smul, toA_smulP, toA_smulP, ← h1, ← h2, hab]
      ring

theorem locL_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : ∀ i ∈ J, x i ≠ 0)
    (z : LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) :
    locL x η S n0 d0 g0 J hJ (locRes h z) = locL x η S n0 d0 g0 I (fun i hi => hJ i (h hi)) z := by
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    apply locL_mk_eq
    exact phi_mul_locL_mk x η S n0 d0 g0 I _ m s

theorem subsingleton_loc {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) := by
  have hkill : ∀ m : TMod x η S n0 d0 g0, (X i : Poly (Sy S r) N) • m = 0 := by
    intro m
    apply Subtype.ext
    apply (toA x η).injective
    rw [Submodule.coe_smul, toA_smulP, phi_X, hx, single_zero, zero_mul, Submodule.coe_zero, map_zero]
  refine ⟨fun a b => ?_⟩
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
      change (X i : Poly (Sy S r) N) • (s' : Poly (Sy S r) N) • m =
        (X i : Poly (Sy S r) N) • (s : Poly (Sy S r) N) • m'
      rw [smul_comm, hkill, smul_zero, smul_comm, hkill, smul_zero]

def idx0 (i : Fin (N + 1)) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩

theorem mem_chartCell_ne_zero {i0 : Fin (N + 1)} (hi0 : x i0 ≠ 0) : ∀ i ∈ (idx0 i0).1.1, x i ≠ 0 := by
  intro i hi
  rw [Finset.mem_singleton.mp hi]
  exact hi0

def evalIdx (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0) locResS 0
      →ₗ[Sy S r] Amb x η where
  toFun z := locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
    ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0))
  map_add' a b := by
    rw [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
  map_smul' c z := by
    rw [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact LinearMap.map_smul_of_tower _ _ _

def readChartH0 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    cohom (tgraded x η S n0 d0 g0) 0 0 →ₗ[Sy S r] Amb x η :=
  Submodule.liftQ _ (evalIdx x η S n0 d0 g0 i0 hi0) (by
      intro z hz
      have h0 : (z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) = 0 := by
        simpa [Cech.bdryDeg] using hz
      rw [LinearMap.mem_ker]
      change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
        ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0)) = 0
      rw [h0, Pi.zero_apply, map_zero])

theorem mem_range_readChartH0 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) (t : Amb x η)
    (ht : ∀ (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0), ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = t) :
    t ∈ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
  classical
  let v : ∀ I : StdCell N, LocMod (Sy S r) N (TMod x η S n0 d0 g0) I.1 := fun I =>
    if hI : ∀ i ∈ I.1, x i ≠ 0 then (ht I hI).choose else 0
  have hv : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    by_cases hJ : ∀ i ∈ J.1, x i ≠ 0
    · have hI : ∀ i ∈ I.1, x i ≠ 0 := fun i hi => hJ i (h hi)
      apply locL_injective x η S n0 d0 g0 J.1 hJ
      change locL x η S n0 d0 g0 J.1 hJ (locRes h (v I)) = locL x η S n0 d0 g0 J.1 hJ (v J)
      rw [locL_locRes]
      simp only [v, dif_pos hI, dif_pos hJ]
      rw [(ht I hI).choose_spec.2, (ht J hJ).choose_spec.2]
    · push Not at hJ
      obtain ⟨i, hi, hx⟩ := hJ
      have := subsingleton_loc x η S n0 d0 g0 hi hx
      exact Subsingleton.elim _ _
  have hcoc : (fun I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => v I.1) ∈
      Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0)
        locResS 0 := by
    refine ⟨Cech.d_zero_of_compat v hv, fun I _ => ?_⟩
    by_cases hI : ∀ i ∈ I.1.1, x i ≠ 0
    · simp only [v, dif_pos hI]; exact (ht I.1 hI).choose_spec.1
    · simp only [v, dif_neg hI]; exact zero_mem _
  refine ⟨Submodule.Quotient.mk ⟨_, hcoc⟩, ?_⟩
  change evalIdx x η S n0 d0 g0 i0 hi0 ⟨_, hcoc⟩ = t
  change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0) (v (idx0 i0).1) = t
  simp only [v, dif_pos (mem_chartCell_ne_zero x hi0)]
  exact (ht _ (mem_chartCell_ne_zero x hi0)).choose_spec.2

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.CoeffPsiMulSingle

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

theorem map_C_mem_monos {I : Finset (Fin (N + 1))} {t : Poly S N} (ht : t ∈ monos (S := S) I) :
    MvPolynomial.map (C : S →+* Sy S r) t ∈ monos (S := Sy S r) I := by
  induction ht using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]; exact X_mem_monos (Finset.mem_coe.mp hi)
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem single_mem_TMod (M0 : FinGradedSub (S := S) (x := x) Ω)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    {a : ℤ} {m : Ω} (hm : m ∈ M0.piece a) :
    (toA x η).symm (single (a, (0 : ℤ)) m) ∈ TMod x η S n0 d0 g0 := by
  suffices key : ∀ z ∈ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = a ∧ z = aeval x f • g0 j},
      (toA x η).symm (single (a, (0 : ℤ)) z) ∈ TMod x η S n0 d0 g0 from key m (hspan a hm)
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, f, e, hf, he, rfl⟩ := hz
    have : (toA x η).symm (single (a, (0 : ℤ)) (aeval x f • g0 j)) =
        (MvPolynomial.map (C : S →+* Sy S r) f : Poly (Sy S r) N) • genT x η n0 d0 g0 j := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, genT, AddEquiv.apply_symm_apply, phi_map_C x η S hf,
        single_mul_single, smul_eq_mul, ← he]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => rw [single_zero, map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [single_add, map_add (f := _)]; exact add_mem hp hq
  | smul s p _ hp =>
    have : (toA x η).symm (single (a, (0 : ℤ)) (s • p)) =
        (C (C s) : Poly (Sy S r) N) • (toA x η).symm (single (a, (0 : ℤ)) p) := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, AddEquiv.apply_symm_apply, phi_C, psi, aeval_C,
        algebraMap_LA, single_mul_single, Algebra.smul_def]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hp

def toChart (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) : Chart x :=
  ⟨I.1, I.2.1, fun i hi => (mem_support x).mpr (hI i hi)⟩

theorem pow_sub_le (B : SubSystem S x Ω)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (I : Chart x) (b : ℕ) :
    (B.pow b).sub I ≤ Submodule.span (chartRing S x I)
      {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} := by
  induction b with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨1, isHomogeneous_one _ _, by simp⟩)
  | succ b ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hgen I] at hq
    have hmul : q * y ∈ Submodule.span (chartRing S x I) (Set.range η) *
        Submodule.span (chartRing S x I)
          {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} :=
      Submodule.mul_mem_mul hq (ih hy)
    rw [Submodule.span_mul_span] at hmul
    rw [smul_eq_mul]
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨X j * h, ?_, by rw [map_mul, aeval_X]⟩
    simpa [add_comm] using (isHomogeneous_X S j).mul hh

variable (M0 : FinGradedSub (S := S) (x := x) Ω)

def genSet (I : Chart x) (b : ℕ) : Set Ω :=
  {ω | ∃ (f : Poly S N) (e : ℕ) (h : MvPolynomial (Fin (r + 1)) S) (m : Ω) (a : ℤ) (t : Poly S N) (e' : ℕ),
    f.IsHomogeneous e ∧ h.IsHomogeneous b ∧ m ∈ M0.piece a ∧ t ∈ monos (S := S) I.1 ∧
    t.IsHomogeneous e' ∧ (e' : ℤ) = e + a ∧ ω = aeval x f * aeval η h * m / aeval x t}

theorem chart_mul_mem_span (I : Chart x) (b : ℕ) (c : chartRing S x I) {ω : Ω}
    (hω : ω ∈ Submodule.span S (genSet x η S M0 I b)) :
    (c : Ω) * ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  obtain ⟨f', t', e'', ht', hf', hte', hc⟩ := c.2
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hz
    refine Submodule.subset_span ⟨f' * f, e'' + e, h, m, a, t' * t, e'' + e', hf'.mul hf, hh, hm,
      mul_mem ht' ht, hte'.mul hte, by push_cast; omega, ?_⟩
    rw [hc]
    have h1 := eval_ne_zero_of_mem_monos I ht'
    have h2 := eval_ne_zero_of_mem_monos I ht
    simp only [map_mul]
    field_simp
  | zero => rw [mul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [mul_add]; exact add_mem hp hq
  | smul s p _ hp => rw [mul_smul_comm]; exact Submodule.smul_mem _ s hp

theorem twist_sub_le (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I) (I : Chart x) (b : ℕ) :
    ∀ ω ∈ (G.twist (B.pow b)).sub I, ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  let W : Submodule (chartRing S x I) Ω :=
    { carrier := Submodule.span S (genSet x η S M0 I b)
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c ω hω => chart_mul_mem_span x η S M0 I b c hω }
  suffices hle : (G.twist (B.pow b)).sub I ≤ W from fun ω hω => hle hω
  change Submodule.span _ _ ≤ W
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  have hq' := pow_sub_le x η S B.toSubFamily.toSubSystem hgen I b hq
  rw [← hG I] at hy
  have hmul := Submodule.mul_mem_mul hq' hy
  rw [FinGradedSub.tilde, Submodule.span_mul_span] at hmul
  rw [smul_eq_mul]
  refine (Submodule.span_le.mpr ?_) hmul
  rintro _ ⟨_, ⟨h, hh, rfl⟩, _, ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨1, 0, h, m, a, t, e, isHomogeneous_one _ _, hh, hm, ht, hte, by omega, ?_⟩
  rw [map_one, one_mul, smul_eq_mul]
  field_simp

variable {n0 d0 g0} in
theorem gen_pre
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ genSet x η S M0 (toChart x I hI) b) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hω
  let mm : TMod x η S n0 d0 g0 := ⟨_, single_mem_TMod x η S n0 d0 g0 M0 hspan hm⟩
  let p : Poly (Sy S r) N := MvPolynomial.map (C : S →+* Sy S r) f * C h
  have hp : p.IsHomogeneous e := by
    simpa using (hf.map (C : S →+* Sy S r)).mul (isHomogeneous_C (Fin (N + 1)) h)
  have hmm : mm ∈ (tgraded x η S n0 d0 g0).piece a := by
    change toA x η ((toA x η).symm _) ∈ tgr a
    rw [AddEquiv.apply_symm_apply]
    exact single_mem_tgr _ _ _
  have hpm := (tgraded x η S n0 d0 g0).smul_mem e a p mm hp hmm
  let s : monos (S := Sy S r) I.1 := ⟨MvPolynomial.map (C : S →+* Sy S r) t, map_C_mem_monos S ht⟩
  refine ⟨(LocalizedModule.mk (p • mm) s : LocalizedModule (monos (S := Sy S r) I.1) (TMod x η S n0 d0 g0)),
    Submodule.subset_span ⟨p • mm, s, a + e, e', hpm, hte.map _, by omega, rfl⟩, ?_⟩
  apply locL_mk_eq
  rw [AddEquiv.apply_symm_apply]
  change phi x η S (MvPolynomial.map (C : S →+* Sy S r) t) * _ = toA x η (p • (mm : Amb x η))
  rw [toA_smulP, AddEquiv.apply_symm_apply, phi_map_C x η S hte, map_mul, phi_map_C x η S hf, phi_C,
    psi_of_isHomogeneous η S hh]
  simp only [single_mul_single]
  have ht0 := eval_ne_zero_of_mem_monos (toChart x I hI) ht
  congr 1
  · ext
    · simp; omega
    · simp
  · field_simp


variable {n0 d0 g0} in
theorem chart_pre (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ (G.twist (B.pow b)).sub (toChart x I hI)) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  have h1 := twist_sub_le x η S M0 G B hgen hG (toChart x I hI) b ω hω
  clear hω
  induction h1 using Submodule.span_induction with
  | mem z hz => exact gen_pre x η S M0 hspan I hI b hz
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, single_zero, map_zero]⟩
  | add p q _ _ hp hq =>
    obtain ⟨z1, hz1, e1⟩ := hp
    obtain ⟨z2, hz2, e2⟩ := hq
    exact ⟨z1 + z2, add_mem hz1 hz2, by rw [map_add (f := _), e1, e2, single_add, map_add (f := _)]⟩
  | smul s p _ hp =>
    obtain ⟨z1, hz1, e1⟩ := hp
    refine ⟨(C s : Sy S r) • z1, Submodule.smul_mem _ _ hz1, ?_⟩
    rw [LinearMap.map_smul_of_tower, e1]
    apply (toA x η).injective
    rw [toA_smulSy, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, psi, aeval_C, algebraMap_LA,
      single_mul_single, Algebra.smul_def]
    simp

theorem coeff_psi_mul_single (c : Sy S r) (b' b : ℕ) (s' : Ω) :
    (psi η S c * single ((0 : ℤ), (b' : ℤ)) s').coeff ((0 : ℤ), (b : ℤ)) =
      ∑ d ∈ Finset.range (c.totalDegree + 1),
        if d + b' = b then aeval η (homogeneousComponent d c) * s' else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent c]

  rw [map_sum, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [psi_of_isHomogeneous η S (homogeneousComponent_isHomogeneous d c), single_mul_single, coeff_single,
    Finsupp.single_apply]
  by_cases hdb : d + b' = b
  · rw [if_pos hdb, if_pos (by ext <;> simp; omega)]
  · rw [if_neg hdb, if_neg (by intro h; apply hdb; have := congrArg Prod.snd h; simp at this; omega)]

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
end
end
