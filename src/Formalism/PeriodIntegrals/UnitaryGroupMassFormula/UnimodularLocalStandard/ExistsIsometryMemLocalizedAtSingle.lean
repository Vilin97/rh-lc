module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsGoodForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Imports
public import Mathlib.Analysis.CStarAlgebra.Classes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SelfDualStd
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.StdHSingleZero
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SatStdOfAll

section

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma altE_single (L : PeriodPair) (v : m → ℂ) (n : ℕ) (j : m) (w : ℂ) :
    altE (stdH L m) v (n • Pi.single j w) = (n : ℝ) * (v j * conj w).im / area L := by
  classical
  unfold altE
  rw [stdH_apply]
  have hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w) := by
    rw [Finset.sum_eq_single j]
    · simp [nsmul_eq_mul]
      ring
    · intro i _ hi
      simp [hi]
    · simp
  rw [hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]

lemma alpha_eq (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma theta_alpha_eq (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (-(lam * y)) * hn

lemma coord_mem (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) (n : ℕ) (w : ℂ)
    (h1 : ∃ k : ℤ, (n : ℝ) * (w * conj (lam * ((x * a : ℂ) + y * cmTheta b d))).im
      / area (cmL a b d ha hd lam hlam) = k)
    (h2 : ∃ k : ℤ, (n : ℝ) * (w * conj (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))).im
      / area (cmL a b d ha hd lam hlam) = k) :
    ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w ∈ (cmL a b d ha hd lam hlam).lattice := by
  set L := cmL a b d ha hd lam hlam with hL
  obtain ⟨s, t, hz⟩ := coords L ((n : ℂ) * w)
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hnim : ∀ u : ℂ, (n : ℝ) * (w * u).im = (((n : ℂ) * w) * u).im := by
    intro u
    rw [mul_assoc]
    simp [Complex.mul_im]
  rw [hnim, hz, alpha_eq (ha := ha) (hd := hd) (hlam := hlam), im_mul_conj] at hk1
  rw [hnim, hz, theta_alpha_eq (ha := ha) (hd := hd) (hlam := hlam) hn, im_mul_conj] at hk2
  obtain ⟨j1, hj1⟩ := int_of_div L hk1
  obtain ⟨j2, hj2⟩ := int_of_div L hk2
  push_cast at hj1 hj2
  have hQs : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * s = ((-(y * c * j1 + x * j2) : ℤ) : ℝ) := by
    push_cast
    linear_combination (-((y : ℝ) * c)) * hj1 + (-(x : ℝ)) * hj2
  have hQt : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * t =
      (((x * a + y * b) * j1 - y * j2 : ℤ) : ℝ) := by
    push_cast
    linear_combination ((x : ℝ) * a + y * b) * hj1 + (-(y : ℝ)) * hj2
  rw [show ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w =
      ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) * ((n : ℂ) * w) by push_cast; ring, hz]
  refine (lattice_iff L _).mpr ⟨-(y * c * j1 + x * j2), (x * a + y * b) * j1 - y * j2, ?_⟩
  have cs := congrArg (fun r : ℝ => (r : ℂ)) hQs
  have ct := congrArg (fun r : ℝ => (r : ℂ)) hQt
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast] at cs ct
  simp only [Complex.real_smul, Complex.ofReal_intCast]
  linear_combination L.ω₁ * cs + L.ω₂ * ct

lemma sat_std_of_all (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) (x y : ℤ)
    (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (Λ : AddSubgroup (m → ℂ))
    (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ v ∈ Λ, cmTheta b d • v ∈ Λ)
    (hall : ∀ j, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) :
    ∃ n : ℕ, ¬ l ∣ n ∧ ∀ v ∈ Λ, n • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  have hn := theta_norm hok.1
  have hall' : ∀ j, ∃ N : ℕ, ¬ l ∣ N ∧
      N • (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) ∈ Λ := hall
  choose N hNl hNmem using hall'
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  refine ⟨Q.natAbs * Q.natAbs * ∏ j, N j, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hl).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hl).mp h with h' | h' <;> exact hQ (Int.natCast_dvd.mpr h')
    · obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp h
      exact hNl j hj
  · intro v hv
    have hvd : v ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
      rw [hsd]
      exact hv
    rw [mem_dualLat_iff] at hvd
    rw [mem_stdLat_iff]
    intro i
    have e1 := hvd _ (hNmem i)
    have e2 := hvd _ (hθ _ (hNmem i))
    have hsm : cmTheta b d • (N i • Pi.single i (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) =
        N i • Pi.single i (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [nsmul_eq_mul]
        ring
      · simp [hk]
    rw [altE_single] at e1
    rw [hsm, altE_single] at e2
    have hm := coord_mem hn x y (N i) (v i) e1 e2
    have hmem : ((N i : ℤ) * Q) • v i ∈ (cmL a b d ha hd lam hlam).lattice := by
      rw [zsmul_eq_mul]
      exact_mod_cast hm
    have hnZ : ((Q.natAbs * Q.natAbs * ∏ j, N j : ℕ) : ℤ) =
        (Q * ∏ j ∈ Finset.univ.erase i, (N j : ℤ)) * ((N i : ℤ) * Q) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast
      rw [abs_mul_abs_self]
      ring
    rw [Pi.smul_apply, ← natCast_zsmul, hnZ, mul_smul]
    exact Submodule.smul_mem _ _ hmem

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsIsometryMemLocalizedAtSingle

section

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

lemma isKv_of_sat {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by
  obtain ⟨n, hln, hn⟩ := hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hln (dvd_zero l)
  set S := stdLat (cmL a b d ha hd lam hlam) m
  have hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ :=
    AddSubgroup.nsmul_index_mem _ _
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul] at hmem
  have hN : (S.addSubgroupOf Λ).index * n ≠ 0 := mul_ne_zero h1 hn0
  exact isKv_of_nsmul hN (isKv_of_mem hmem)

lemma exists_isometry_memLocalizedAt_single (hkey : KeyRep) (hok : CmOK a b c d) (m : Type) [Fintype m] [DecidableEq m]
    (Λa : AddSubgroup (m → ℂ)) (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa)
    (hθ : ∀ x ∈ Λa, cmTheta b d • x ∈ Λa)
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0)
    (h2 : relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m) :
    ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      ∀ j ∈ T, SatMem l (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
  classical
  have himg : ∀ (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)), (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) →
      ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ := by
    intro g Λ hΛ z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λ z).1 hz
    exact (mem_imgLat_iff g Λ _).2 ⟨_, hΛ w hw, map_smul g _ w⟩
  have hαK : (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam = (x * a : ℂ) + y * cmTheta b d := by
    field_simp
  have hα0 : lam * ((x * a : ℂ) + y * cmTheta b d) ≠ 0 := by
    intro h0
    rw [alpha_eq (ha := ha) (hd := hd) (hlam := hlam)] at h0
    obtain ⟨hx0, hy0⟩ := LinearIndependent.pair_iff.1 (cmL a b d ha hd lam hlam).indep _ _ h0
    have hx : x = 0 := by exact_mod_cast hx0
    have hy : y = 0 := by exact_mod_cast hy0
    apply hQ
    simp [hx, hy]
  induction T using Finset.induction_on with
  | empty =>
    have hid : ∀ Λ : AddSubgroup (m → ℂ),
        imgLat ((LinearEquiv.refl ℂ (m → ℂ) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ = Λ := by
      intro Λ
      ext z
      rw [mem_imgLat_iff]
      simp
    refine ⟨LinearEquiv.refl ℂ (m → ℂ), fun _ _ => rfl, ?_, ?_, by simp⟩
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
  | insert i₀ T hi₀ ih =>
    obtain ⟨g, hgI, hg1, hg2, hgT⟩ := ih
    have hc := comm_img g hg1 hg2 h1 h2
    have hsd' := selfDual_img _ g hgI hsd
    have hθ' := himg g Λa hθ
    obtain ⟨v, hvS, hvT, hvv⟩ := hkey a b c d ha hd lam hlam hok m _ hsd' hθ' hc.1 hc.2 l hl x y hQ T i₀ hi₀ hgT
    have hvK : IsKv b d lam v := isKv_of_sat hl hc.1 hvS
    have hK : ∀ s : ℂ, s = 1 ∨ s = -1 →
        IsK b d (s * (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam) := by
      intro s hs
      have hb : IsK b d ((x * a : ℂ) + y * cmTheta b d) :=
        ⟨x * a, y, 1, one_ne_zero, by push_cast; ring⟩
      rcases hs with rfl | rfl
      · rw [one_mul, hαK]
        exact hb
      · rw [neg_one_mul, neg_div, hαK]
        exact isK_neg hb
    have hee : stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
        (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) ≠ 0 := by
      rw [stdH_kappa _ hlam, Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same]
      exact mul_ne_zero (kappa_ne _ hlam)
        (mul_ne_zero (div_ne_zero hα0 hlam) ((map_ne_zero _).2 (div_ne_zero hα0 hlam)))
    obtain ⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) ≠ 0 := by
      by_cases h : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (1 * (lam * ((x * a : ℂ) + y * cmTheta b d)))) = 0
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, Pi.single_neg, map_neg]
        rw [one_mul, sub_eq_zero] at h
        rw [sub_neg_eq_add, ← h, ← two_mul, hvv]
        exact mul_ne_zero two_ne_zero hee
      · exact ⟨1, Or.inl rfl, h⟩
    have hss : s * s = 1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hvv' : stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d))))
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) := by
      rw [hvv]
      rcases hs with rfl | rfl
      · simp only [one_mul]
      · simp only [neg_one_mul, Pi.single_neg, map_neg, LinearMap.neg_apply, neg_neg]
    obtain ⟨σ, hσI, hσ1, hσ2, hσv, hσfix⟩ :=
      qrefl_to hok v _ hvv' hne hvK (isKv_single (hK s hs) i₀)
    refine ⟨g.trans σ, isom_trans _ g σ hgI hσI, ?_, ?_, ?_⟩
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).1
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).2
    · intro j hj
      rw [imgLat_trans]
      rcases Finset.mem_insert.1 hj with rfl | hjT
      · obtain ⟨n, hln, hn⟩ := hvS
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨s • n • v, ?_, ?_⟩⟩
        · rcases hs with rfl | rfl
          · rwa [one_smul]
          · rw [neg_one_smul]
            exact AddSubgroup.neg_mem _ hn
        · rw [map_smul, map_nsmul, hσv, smul_comm, ← Pi.single_smul', smul_eq_mul, ← mul_assoc, hss, one_mul]
      · obtain ⟨n, hln, hn⟩ := hgT j hjT
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨_, hn, ?_⟩⟩
        rw [map_nsmul, hσfix]
        apply stdH_single_zero
        have hne' : j ≠ i₀ := fun h => hi₀ (h ▸ hjT)
        simp [hvT j hjT, Pi.single_eq_of_ne hne']

theorem stepB_of_key (hkey : KeyRep) : StepB := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨x, y, hQ⟩ := exists_good_form hok hl
  obtain ⟨g, hgI, hg1, hg2, hgT⟩ := exists_isometry_memLocalizedAt_single hkey hok m Λa hsd hθ h1 h2 hl x y hQ Finset.univ
  have hc := comm_img g hg1 hg2 h1 h2
  have hsd' := selfDual_img _ g hgI hsd
  have hθ' : ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λa z).1 hz
    exact (mem_imgLat_iff g Λa _).2 ⟨_, hθ w hw, map_smul g _ w⟩
  obtain ⟨n, hln, hn⟩ := sat_std_of_all hok hl x y hQ _ hsd' hθ' (fun j => hgT j (Finset.mem_univ j))
  refine ⟨g, hgI, hc.1, ?_, hc.2⟩
  intro hdvd
  have hfi : ((stdLat (cmL a b d ha hd lam hlam) m).addSubgroupOf
      (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)).FiniteIndex := ⟨hc.1⟩
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
  have hnq : n • q = 0 := by
    induction q using QuotientAddGroup.induction_on with
    | H w =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul]
      exact hn w w.2
  have h := addOrderOf_dvd_of_nsmul_eq_zero hnq
  rw [hq] at h
  exact hln h

theorem target_of_key (hkey : KeyRep) : PI.UnimodLocStd := target_of (stepB_of_key hkey) stepC

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
end
