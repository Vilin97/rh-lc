module

public import GroundTheory.PAdicHodge.BCrisEigen
public import GroundTheory.PAdicHodge.SenTateCharClosure
import GroundTheory.LocalFields.Examples
import GroundTheory.LocalFields.PadicLogSeries
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic
public import GroundTheory.PAdicHodge.SenTateCharTrace
import GroundTheory.PAdicHodge.SenTateCharUnitPow
public import GroundTheory.LocalFields.ConductorMatch
public import GroundTheory.PAdicHodge.FieldOfNormsRam
public import GroundTheory.PAdicHodge.SenTateCharLevels

-- Source module: GroundTheory.PAdicHodge.SenTateCharQp

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge
end
end
end

-- Source module: GroundTheory.PAdicHodge.SenTateCharacters

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open CyclNorms GroundTheory.LocalField ValuativeRel SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]

namespace SenTateChar

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
  {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

theorem eq_zero_of_mem_inertiaGal (hη : Continuous η) {τ : Gal(PadicAlgCl p/K)}
    (hτ : τ ∈ inertiaGal K) (hτ2 : η τ ∈ unitsOneAdd p 2) (hτ1 : η τ ≠ 1) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  have hA := artinImage_ne_bot hη hτ hτ2 hτ1
  have hfin : ∀ k, FiniteDimensional K (charTower η k) := fun k => finiteDimensional_charTower hη k
  have : IsAbelianGalois K (charTower η 2) := isAbelianGalois_charTower hη 2

  have h2 : ∀ n, conductor (charTower η 2) ≤ n → 2 ≤ artinLevel K η n := by
    intro n hn
    obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n)
    have ha2 := artinImage_le_of_conductor_le hη hn ha
    by_contra hlt
    push Not at hlt
    exact ha' (unitsOneAdd_antitone (by omega) ha2)

  obtain ⟨n₁, hn₁⟩ := exists_map_pow_unitFiltrationUnits (K := K) p
  set n₀ := max (conductor (charTower η 2)) n₁
  have hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1 :=
    fun n hn => artinLevel_add hη hA (h2 n (le_of_max_le_left hn)) (hn₁ n (le_of_max_le_right hn))
  have h2₀ : 2 ≤ artinLevel K η n₀ := h2 n₀ (le_max_left _ _)

  obtain ⟨b, hb, hb'⟩ := exists_level hτ1
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) hτ2)

  set π : PadicAlgCl p := algebraMap K (PadicAlgCl p) (baseUnif K : K)
  set C : ℝ := ‖π ^ (-(2 * absRamificationIndex K : ℤ))‖
  have hbound : ∀ n, max (artinLevel K η n₀) b ≤ n → ∀ m, ∀ y ∈ charTower η m,
      ‖normTrace (charTower η n) y‖ ≤ C * ‖y‖ := by
    intro n hn m y hy
    have h := nrm_normTrace_charTower_le hη hA le_rfl h2₀ hper hb2 hb hb'
      (le_of_max_le_right hn) (le_of_max_le_left hn) hy
    have e : baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) =
        nrm K (π ^ (-(2 * absRamificationIndex K : ℤ))) := by
      rw [nrm_zpow, ← Real.rpow_intCast]
      push_cast
      rfl
    rw [e, ← nrm_mul, nrm_le_nrm_iff_norm_le', norm_mul] at h
    exact h
  refine eq_zero_of_tower K η (charTower η) (charTower_mono η)
    (fun σ k y hy => map_mem_charTower hη σ hy) (fun σ hσ => ?_) C (max (artinLevel K η n₀) b)
    hbound (fun n hn => ?_) hx
  · refine eq_one_of_forall_mem_unitsOneAdd fun k => ?_
    have := hσ k
    rwa [fixingSubgroup_charTower hη, mem_charTowerGal] at this
  · obtain ⟨h1, h1'⟩ := pow_prime_pow_mem_not_mem hb2 hb hb' (n - b)
    rw [Nat.add_sub_cancel' (le_of_max_le_right hn)] at h1 h1'
    refine ⟨τ ^ p ^ (n - b), ?_, ?_⟩
    · rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_pow]
      exact h1
    · rw [map_pow]
      intro h
      exact h1' (h ▸ one_mem _)

end SenTateChar

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

theorem finite_image_inertiaGal_of_invariant (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  by_contra hinf
  obtain ⟨τ, hτ, hτ2, hτ1⟩ := exists_mem_inertiaGal_unitsOneAdd_two K η hη hinf
  obtain ⟨x, hx0, hx⟩ := hx
  exact hx0 (eq_zero_of_mem_inertiaGal hη hτ hτ2 hτ1 hx)

theorem finite_image_inertiaGal_of_invariant_padic (η : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] (η σ : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  obtain ⟨η', hη', hηη'⟩ := exists_continuous_units_padicInt_lift η hη
  have h := finite_image_inertiaGal_of_invariant K η' hη' (by
    obtain ⟨x, hx0, hx⟩ := hx
    exact ⟨x, hx0, fun σ => by rw [hηη']; exact hx σ⟩)
  refine (h.image (Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨η' σ, ⟨σ, hσ, rfl⟩, ?_⟩
  ext
  rw [Units.coe_map, ← hηη' σ]
  rfl

end GroundTheory.PAdicHodge
end
end
end

-- Source module: GroundTheory.PAdicHodge.BCrisRegularSenTate

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_inertiaGal_of_forall_unramifiedClosure {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {σ : Gal(PadicAlgCl p/K)} (hσ : ∀ u ∈ unramifiedClosure p, σ u = u) : σ ∈ inertiaGal K := by
  intro y hy
  have hc : ‖(y : ℂ_[p])‖ ≤ 1 := by rwa [PadicComplex.norm_extends]
  obtain ⟨k, hk⟩ := eventually_approx_pow hc 1
  obtain ⟨u, hu, hyu⟩ := hk k le_rfl
  set n := p ^ k with hn
  have hpn : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends]
    congr 1
    simp
  have hd : ‖y ^ n - u‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends, ← hpn]
    have e : ((y ^ n - u : PadicAlgCl p) : ℂ_[p]) = (y : ℂ_[p]) ^ n - (u : ℂ_[p]) := by
      simp only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]
    rw [e]
    simpa using hyu
  have hσn : ‖σ y ^ n - y ^ n‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    have e : σ y ^ n - y ^ n = σ (y ^ n - u) - (y ^ n - u) := by
      rw [map_sub, map_pow, hσ u hu]
      ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hd)
    rw [norm_gal_apply]
    exact hd
  have hσy : ‖σ y‖ ≤ 1 := by rwa [norm_gal_apply]
  have hdiff : ‖σ y - y‖ ≤ 1 := (norm_sub_le_max_of_ultrametric _ _).trans (max_le hσy hy)
  let a : normInteger (PadicAlgCl p) := ⟨σ y - y, mem_normInteger.2 hdiff⟩
  let b : normInteger (PadicAlgCl p) := ⟨y, mem_normInteger.2 hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out a b k
  have hr' := congrArg (fun z : normInteger (PadicAlgCl p) => (z : PadicAlgCl p)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, a, b,
    sub_add_cancel] at hr'
  have e : (σ y - y) ^ n = (σ y ^ n - y ^ n) - (p : PadicAlgCl p) * (σ y - y) * y * r := by
    rw [hn, hr']
    ring
  have hr1 : ‖(r : PadicAlgCl p)‖ ≤ 1 := mem_normInteger.1 r.2
  have hlt : ‖σ y - y‖ ^ n < 1 := by
    rw [← norm_pow, e]
    refine (norm_sub_le_max_of_ultrametric (σ y ^ n - y ^ n)
      ((p : PadicAlgCl p) * (σ y - y) * y * r)).trans_lt (max_lt (hσn.trans_lt
      norm_natCast_p_algCl_lt_one) ?_)
    rw [norm_mul, norm_mul, norm_mul]
    rw [mul_assoc, mul_assoc]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg (p : PadicAlgCl p)) ?_)
      (norm_natCast_p_algCl_lt_one (p := p))
    exact mul_le_one₀ hdiff (by positivity) (mul_le_one₀ hy (norm_nonneg _) hr1)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hp.out.ne_zero)).1 hlt

namespace ACris

theorem senTateCharacters : SenTateCharacters p := by
  intro K _ η hη x hx0 hx
  have hfin := finite_image_inertiaGal_of_invariant_padic K η⁻¹
    (show Continuous fun σ => (η σ)⁻¹ from hη.inv) ⟨x, hx0, fun σ => by
      rw [hx σ, ← mul_assoc, ← map_mul, MonoidHom.inv_apply, Units.inv_mul, map_one, one_mul]⟩
  refine (hfin.image (·⁻¹)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  exact ⟨η⁻¹ σ, ⟨σ, mem_inertiaGal_of_forall_unramifiedClosure hσ, rfl⟩, by simp⟩

end ACris

end GroundTheory.PAdicHodge
end
end
end
