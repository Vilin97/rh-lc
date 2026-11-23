module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropicStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstancesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPoint

section

@[expose] public section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo


open FirstMinPos in
theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPointStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  first | exact @GlobalTheory.CuspGeo.firstMin_pos | exact GlobalTheory.CuspGeo.firstMin_pos | (intros; apply GlobalTheory.CuspGeo.firstMin_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroupStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup : ∀ I : AutInst, HtMin I := by
  first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo

theorem exists_scale_of_bdd {ι : Type*} (N : ι → ℝ) (t a : ℝ) (ht : 0 < t) (hN : ∀ i, t ≤ N i) (ha : 0 < a) :
    ∃ m : ℝ, 0 < m ∧ m ≤ a ∧ (∀ i, m / 2 ≤ N i) ∧ (m = a ∨ ∃ i, N i ≤ m) := by
  by_cases h : ∃ i, N i ≤ a
  · obtain ⟨i₀, hi₀⟩ := h
    have hbdd : BddBelow (Set.range N) := ⟨t, by rintro _ ⟨i, rfl⟩; exact hN i⟩
    haveI : Nonempty ι := ⟨i₀⟩
    have hl : t ≤ ⨅ i, N i := le_ciInf hN
    have hle : ∀ i, ⨅ i, N i ≤ N i := fun i => ciInf_le hbdd i
    refine ⟨min (2 * ⨅ i, N i) a, lt_min (by linarith) ha, min_le_right _ _, fun i => ?_, ?_⟩
    · have h1 := hle i
      have h2 := min_le_left (2 * ⨅ i, N i) a
      linarith
    · rcases le_total (2 * ⨅ i, N i) a with h2 | h2
      · right
        rw [min_eq_left h2]
        obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt (show ⨅ i, N i < 2 * ⨅ i, N i by linarith)
        exact ⟨i, hi.le⟩
      · left
        exact min_eq_right h2
  · push_neg at h
    exact ⟨a, ha, le_rfl, fun i => by linarith [h i], Or.inl rfl⟩

theorem exists_root_scale (n : ℕ) (s₀ m : ℝ) (hs : 0 < s₀) (hm : 0 < m) :
    ∃ η : ℝ, 0 < η ∧ s₀ * η ^ (n + 1) = m := by
  refine ⟨(m / s₀) ^ ((((n + 1 : ℕ) : ℝ))⁻¹), Real.rpow_pos_of_pos (div_pos hm hs) _, ?_⟩
  rw [Real.rpow_inv_natCast_pow (div_pos hm hs).le (Nat.succ_ne_zero n)]
  field_simp

theorem exists_scale_real (I : AutInst) (y : I.Ginf) (s₀ η₀ : ℝ) (hs : 0 < s₀) (hη : 0 < η₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₀ ∧ NoShort I y (s₀ / 2 * η ^ (I.n + 1)) ∧
      (η₀ ≤ η ∨ ∃ u, IntVec I u ∧ u ≠ 0 ∧ ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1)) := by
  obtain ⟨t, ht, hNS⟩ := GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint I y
  obtain ⟨m, hm0, hma, hmN, hmc⟩ := exists_scale_of_bdd (ι := {u // IntVec I u ∧ u ≠ 0})
    (fun u => ‖vec I y u.1‖) t (s₀ * η₀ ^ (I.n + 1)) ht (fun u => hNS u.1 u.2.1 u.2.2) (by positivity)
  obtain ⟨η, hη0, hηm⟩ := exists_root_scale I.n s₀ m hs hm0
  have hpow : η ^ (I.n + 1) ≤ η₀ ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm]; exact hma) hs
  refine ⟨η, hη0, (pow_le_pow_iff_left₀ hη0.le hη.le (Nat.succ_ne_zero _)).1 hpow, fun u hu hu0 => ?_, ?_⟩
  · have h1 := hmN ⟨u, hu, hu0⟩
    have h2 : s₀ / 2 * η ^ (I.n + 1) = m / 2 := by rw [← hηm]; ring
    rw [h2]
    exact h1
  · rcases hmc with h | ⟨⟨u, hu, hu0⟩, hle⟩
    · left
      have : η₀ ^ (I.n + 1) ≤ η ^ (I.n + 1) := le_of_mul_le_mul_left (by rw [hηm, h]) hs
      exact (pow_le_pow_iff_left₀ hη.le hη0.le (Nat.succ_ne_zero _)).1 this
    · right
      exact ⟨u, hu, hu0, hηm ▸ hle⟩

theorem close_mono (I : AutInst) {u : I.Ginf} {a b : ℝ} (h : Close I u a) (hab : a ≤ b) : Close I u b :=
  fun v i j => (h v i j).trans hab

end GlobalTheory.CuspGeo

noncomputable section

namespace GlobalTheory.CuspGeo


open Formalism.MainNotions.LeviCoordinates in
theorem nearInst : ∀ I : AutInst, NearInst I := by
  intro I Kp hKo
  have hmem : ∀ {g : I.GA}, g ∈ I.GFset ↔ g ∈ rr_GF I := fun {g} => by
    rw [← SetLike.mem_coe, rr_GF_coe]
  obtain ⟨-, -, -, hKsC, hKsO, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  set Kq : Subgroup I.Gf := Kp ⊓ Ks with hKq
  have hKqO : IsOpen (Kq : Set I.Gf) := by
    rw [hKq, Subgroup.coe_inf, hKs]; exact hKo.inter hKsO
  have hKqC : IsCompact (Kq : Set I.Gf) :=
    hKsC.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKqO)
      (by rw [← hKs]; exact fun z hz => (Subgroup.mem_inf.1 hz).2)
  obtain ⟨S, hS⟩ := adelic_class_set_finite I Kq hKqO
  set U : Set I.Gf := {g | ∀ s ∈ S, s⁻¹ * g * s ∈ Kq} with hUdef
  have hU : U ∈ 𝓝 (1 : I.Gf) := by
    have : ∀ s ∈ S, ∀ᶠ g in 𝓝 (1 : I.Gf), s⁻¹ * g * s ∈ Kq := fun s _ =>
      (hKqO.preimage (by fun_prop : Continuous fun g : I.Gf => s⁻¹ * g * s)).mem_nhds (by simp)
    exact (Filter.eventually_all_finset S).2 this
  obtain ⟨s₀, η₀, Cs, hs₀, hη₀, hSC⟩ := GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances I U hU
  obtain ⟨b, CH, KH, hKH, hHt⟩ := GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup I
  set s₁ := min s₀ 1 with hs₁
  set η₁ := min η₀ 1 with hη₁
  have hs₁0 : 0 < s₁ := lt_min hs₀ one_pos
  have hη₁0 : 0 < η₁ := lt_min hη₀ one_pos
  set C := max (CH / (s₁ / 2) ^ b) Cs with hC
  refine ⟨(I.n + 1) * b, C, η₁, (fun p : I.Gf × I.Gf × I.Gf => p.1 * p.2.1 * p.2.2) '' (KH ×ˢ ((S : Set I.Gf) ×ˢ (Kq : Set I.Gf))),
    hη₁0, (hKH.prod (S.finite_toSet.isCompact.prod hKqC)).image (by fun_prop), fun x => ?_⟩
  obtain ⟨γf, ⟨γE, hγE, hγEf⟩, s, hsS, k, hk, hx2⟩ := hS x.2
  set γ₀ : I.GA := (fun v => Formalism.L2.S.S7.DensRat.ratReal I γE hγE v, γf) with hγ₀def
  have hγ₀ : γ₀ ∈ I.GFset := ⟨γE, hγE, fun v => by simp [hγ₀def, Formalism.L2.S.S7.DensRat.ratReal, uMat], hγEf⟩
  set y : I.Ginf := γ₀.1⁻¹ * x.1 with hy
  have hx : x = γ₀ * ((y, s * k) : I.GA) :=
    Prod.ext (by simp [hy]) (by simp [hγ₀def, hx2, mul_assoc])
  obtain ⟨η, hη0, hηle, hNS, hcase⟩ := exists_scale_real I y s₁ η₁ hs₁0 hη₁0
  have hη1 : η ≤ 1 := hηle.trans (min_le_right _ _)
  set t := s₁ / 2 * η ^ (I.n + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have h1 : s₁ ≤ 1 := min_le_right _ _
    have h2 : η ^ (I.n + 1) ≤ 1 := pow_le_one₀ hη0.le hη1
    have h3 : 0 ≤ η ^ (I.n + 1) := by positivity
    nlinarith
  obtain ⟨γ₁, hγ₁, hγ₁K, hγ₁b⟩ := hHt y t ht0 ht1 hNS
  refine ⟨η, hη0, hη1, ⟨γ₁ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem (hmem.1 hγ₁) ((rr_GF I).inv_mem (hmem.1 hγ₀))), ?_, ?_⟩, ?_⟩
  · refine ⟨(γ₁.2, s, k), ⟨hγ₁K, hsS, hk⟩, ?_⟩
    rw [hx]
    simp [mul_assoc]
  · intro v i j
    have e1 : (γ₁ * γ₀⁻¹ * x).1 = γ₁.1 * y := by rw [hx]; simp [mul_assoc]
    rw [e1]
    have hb := hγ₁b v i j
    have hpos : 0 < (s₁ / 2) ^ b := by positivity
    have e2 : t ^ b = (s₁ / 2) ^ b * η ^ ((I.n + 1) * b) := by rw [ht, mul_pow, pow_mul]
    rw [e2] at hb
    have h3 : ‖uMat ((γ₁.1 * y) v) i j‖ * η ^ ((I.n + 1) * b) ≤ CH / (s₁ / 2) ^ b := by
      rw [le_div_iff₀ hpos]; linarith
    exact h3.trans (le_max_left _ _)
  rcases hcase with h | ⟨u, hu, hu0, hul⟩
  · exact Or.inl h
  right
  have hul' : ‖vec I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    hul.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨W, hW, hcov⟩ := hSC y η hη0 (hηle.trans (min_le_left _ _)) ⟨u, hu, hu0, hul'⟩
  obtain ⟨W', hW', hconj⟩ := GlobalTheory.T.rational_conj_unipotentRadical_isotropic I γ₀ hγ₀ W hW
  obtain ⟨⟨N, hN⟩, -, hpart, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  refine ⟨W', hW', fun m hm => ?_⟩
  have hm' : γ₀⁻¹ * m * γ₀ ∈ I.NA W := hconj m hm
  obtain ⟨γ₂, ⟨hγ₂, hγ₂N⟩, hγ₂U⟩ := hdense U hU _ hm'
  set m'' := γ₂⁻¹ * (γ₀⁻¹ * m * γ₀) with hm''
  have hm''N : m'' ∈ I.NA W := by
    rw [← hN] at hm' hγ₂N ⊢
    exact N.mul_mem (N.inv_mem hγ₂N) hm'
  obtain ⟨γ₃, hγ₃, hγ₃U, hclose⟩ := hcov m''.1 (hpart m'' hm''N).1
  refine ⟨γ₀ * γ₂ * γ₃⁻¹ * γ₀⁻¹, hmem.2 ((rr_GF I).mul_mem ((rr_GF I).mul_mem ((rr_GF I).mul_mem (hmem.1 hγ₀)
    (hmem.1 hγ₂)) ((rr_GF I).inv_mem (hmem.1 hγ₃))) ((rr_GF I).inv_mem (hmem.1 hγ₀))),
    y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k), ?_, ?_,
    close_mono I hclose (mul_le_mul_of_nonneg_right (le_max_right _ _) hη0.le)⟩
  · have e : (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k) = k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k := by group
    rw [e]
    have hk' : k⁻¹ * ((s⁻¹ * γ₃.2 * s) * (s⁻¹ * m''.2 * s)) * k ∈ Kq :=
      Kq.mul_mem (Kq.mul_mem (Kq.inv_mem hk) (Kq.mul_mem (hγ₃U s hsS) (hγ₂U s hsS))) hk
    exact (Subgroup.mem_inf.1 hk').1
  · have hyu : ((y, s * k) : I.GA) * (y⁻¹ * (γ₃.1 * m''.1) * y, (s * k)⁻¹ * (γ₃.2 * m''.2) * (s * k)) =
        γ₃ * m'' * (y, s * k) := Prod.ext (by simp; group) (by simp; group)
    have hmm : m = γ₀ * γ₂ * m'' * γ₀⁻¹ := by rw [hm'']; group
    calc m * x = γ₀ * γ₂ * γ₃⁻¹ * (γ₃ * m'' * (y, s * k)) := by rw [hmm, hx]; group
      _ = _ := by rw [← hyu, hx]; group

end GlobalTheory.CuspGeo
end
end
end
end
