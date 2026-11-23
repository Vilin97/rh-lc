module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus
public import GroundTheory.PAdicHodge.BCrisEigen
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PAdicHodge.BCrisPlusInvariants
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Polynomial.Basic
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic

-- Source module: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero

section

@[expose] public section

noncomputable section

namespace period_ring_base

open Formalism.Per6
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

open Topology Filter

namespace BaseB

variable {l : ℕ} [Fact l.Prime]

theorem toBot_one : toBot (1 : GQ l) = 1 := AlgEquiv.ext fun _ => rfl

theorem toBot_mul (g h : GQ l) : toBot (g * h) = toBot g * toBot h := AlgEquiv.ext fun _ => rfl

theorem th_alg (b : BdRp l) : th l (algebraMap (BdRp l) (BdR l) b) = θD l b := by
  have hm : algebraMap (BdRp l) (BdR l) b ∈ Plus l := ⟨b, rfl⟩
  rw [th, dite_eq_left hm]
  congr 1
  exact IsFractionRing.injective (BdRp l) (BdR l) (RingHom.mem_range.1 hm).choose_spec

theorem σD_alg (g : GQ l) (b : BdRp l) :
    σD g (algebraMap (BdRp l) (BdR l) b) = algebraMap (BdRp l) (BdR l) (toBot g • b) :=
  galBdRField_algebraMap _ _

theorem tQ_alg : tQ l = algebraMap (BdRp l) (BdR l) (tBdR l) := DeRhamTwist.Twist.tQ_eq

theorem orbit_alg (y : PadicAlgCl l) : Continuous fun g : GQ l => g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer (GQ l) y
  have hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg
  have h : (g₀⁻¹ * g) • y = y := hg
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

theorem σC_coe (g : GQ l) (y : PadicAlgCl l) : σC g (y : ℂ_[l]) = ((g y : PadicAlgCl l) : ℂ_[l]) := by
  show toBot g • (y : ℂ_[l]) = _
  rw [gal_smul_coe]
  rfl

theorem σC_dist (g : GQ l) (x y : ℂ_[l]) : dist (σC g x) (σC g y) = dist x y :=
  (isometry_smul_gal (toBot g)).dist_eq x y

end BaseB

open BaseB

variable (l : ℕ) [Fact l.Prime]

theorem base_σD_one : ∀ x, σD (1 : GQ l) x = x := by
  intro x
  show galBdRField (toBot 1) x = x
  rw [toBot_one, galBdRField_one]
  rfl

theorem base_σD_mul : ∀ (g h : GQ l) x, σD (g * h) x = σD g (σD h x) := by
  intro g h x
  show galBdRField (toBot (g * h)) x = galBdRField (toBot g) (galBdRField (toBot h) x)
  rw [toBot_mul, galBdRField_mul]
  rfl

theorem base_σC_one : ∀ x, σC (1 : GQ l) x = x := by
  intro x
  show galCp (toBot 1) x = x
  rw [toBot_one, galCp_one]
  rfl

theorem base_σC_mul : ∀ (g h : GQ l) x, σC (g * h) x = σC g (σC h x) := by
  intro g h x
  show galCp (toBot (g * h)) x = galCp (toBot g) (galCp (toBot h) x)
  rw [toBot_mul, galCp_mul]
  rfl

theorem base_σ_u : ∀ g : GQ l, σD g (uQ l) = uQ l + qQ l (κ g) * tQ l := by
  intro g
  show σD g (algebraMap (BdRp l) (BdR l) (uBdR l)) = _
  rw [σD_alg, gal_smul_uBdR_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g), map_add (f := _),
    map_mul, tQ_alg]
  rfl

theorem base_κ_mul : ∀ g h : GQ l, κ (g * h) = κ g + χ g * κ h := by
  intro g h
  simp only [κ, χ]
  rw [toBot_mul, kummerC_mul, DeRhamTwist.Twist.cycloChar_toBot]
  push_cast
  ring

theorem base_plus_σ : ∀ (g : GQ l) x, x ∈ Plus l → σD g x ∈ Plus l := by
  rintro g _ ⟨b, rfl⟩
  exact ⟨toBot g • b, (σD_alg g b).symm⟩

theorem base_th_σ : ∀ (g : GQ l) x, x ∈ Plus l → th l (σD g x) = σC g (th l x) := by
  rintro g _ ⟨b, rfl⟩
  rw [σD_alg, th_alg, th_alg]
  exact thetaBDeRhamPlusField_gal_smul _ _

theorem base_th_add : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x + y) = th l x + th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_add (f := _), th_alg, th_alg, th_alg, map_add (f := _)]

theorem base_th_mul : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x * y) = th l x * th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, th_alg, th_alg, th_alg, map_mul]

theorem base_th_q : ∀ q, qQ l q ∈ Plus l ∧ th l (qQ l q) = algebraMap ℚ_[l] ℂ_[l] q := by
  intro q
  refine ⟨⟨_, rfl⟩, ?_⟩
  show th l (algebraMap (BdRp l) (BdR l) (algebraMap ℚ_[l] (BdRp l) q)) = _
  rw [th_alg]
  exact thetaBDeRhamPlusField_algebraMap l q

theorem base_t_plus : tQ l ∈ Plus l := ⟨ACris.iota ℂ_[l] l (tA l), rfl⟩

theorem base_th_zero : ∀ x ∈ Plus l, (th l x = 0 ↔ ∃ y ∈ Plus l, x = tQ l * y) := by
  rintro _ ⟨b, rfl⟩
  rw [th_alg]
  have hk : θD l b = 0 ↔ b ∈ IsLocalRing.maximalIdeal (BdRp l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]
    rfl
  rw [hk, maximalIdeal_eq_span_tBdR, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨_, ⟨c, rfl⟩, by rw [← hc, tQ_alg, ← map_mul, mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, h⟩
    refine ⟨c, IsFractionRing.injective (BdRp l) (BdR l) ?_⟩
    rw [h, tQ_alg, ← map_mul, mul_comm]

theorem base_val : ∀ x : BdR l, x ≠ 0 → ∃ (i : ℤ) (u v : BdR l), u ∈ Plus l ∧ v ∈ Plus l ∧ u * v = 1 ∧
    x = tQ l ^ i * u := by
  intro x hx
  obtain ⟨i, u, h⟩ := ACris.exists_eq_zpow_mul_unit untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hx
  refine ⟨i, algebraMap (BdRp l) (BdR l) (u : BdRp l), algebraMap (BdRp l) (BdR l) ((u⁻¹ : (BdRp l)ˣ) : BdRp l),
    ⟨_, rfl⟩, ⟨_, rfl⟩, by rw [← map_mul, Units.mul_inv, map_one], ?_⟩
  rw [h, tQ_alg]
  rfl

theorem base_orbit : ∀ x : ℂ_[l], Continuous fun g : GQ l => σC g x := by
  intro x
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 (UniformSpace.Completion.denseRange_coe x) (ε / 3)
    (by positivity)
  have hc := (UniformSpace.Completion.continuous_coe (PadicAlgCl l)).comp (orbit_alg (l := l) y)
  filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto g₀) (ε / 3) (by positivity)] with g hg
  have h1 : dist (((g y : PadicAlgCl l) : ℂ_[l])) (((g₀ y : PadicAlgCl l) : ℂ_[l])) < ε / 3 := hg
  calc dist (σC g x) (σC g₀ x)
      ≤ dist (σC g x) (σC g (y : ℂ_[l])) + dist (σC g (y : ℂ_[l])) (σC g₀ (y : ℂ_[l])) +
          dist (σC g₀ (y : ℂ_[l])) (σC g₀ x) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [σC_dist, σC_dist, σC_coe, σC_coe, dist_comm (y : ℂ_[l]) x]
      linarith

end period_ring_base
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace EstT

variable {l : ℕ} [Fact l.Prime]

theorem qB_mem_ainf (q : ℚ_[l]) : qB l q ∈ Ainf' l := by
  have key : ∀ z : ℤ_[l], qB l (algebraMap ℤ_[l] ℚ_[l] z) ∈ Ainf' l := fun z => by
    have e : qB l (algebraMap ℤ_[l] ℚ_[l] z) = zB l z := IsLocalization.lift_eq _ _
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨ainfMap l (zA l z), rfl⟩)
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ℤ_[l]) q
  have hs : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsu := PadicInt.unitCoeff_spec hs
  set u := PadicInt.unitCoeff hs
  set n := (s : ℤ_[l]).valuation
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have e : IsLocalization.mk' ℚ_[l] z s =
      algebraMap ℤ_[l] ℚ_[l] (z * ↑u⁻¹) * ((l : ℚ_[l])⁻¹) ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, hsu]
    simp only [map_mul, map_pow, map_natCast]
    have hx : ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hl0, one_pow]
    have hu : algebraMap ℤ_[l] ℚ_[l] (↑u⁻¹ : ℤ_[l]) * algebraMap ℤ_[l] ℚ_[l] (u : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap ℤ_[l] ℚ_[l] z) * ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n) * hu -
      algebraMap ℤ_[l] ℚ_[l] z * hx
  show qB l (IsLocalization.mk' ℚ_[l] z s) ∈ _
  rw [e, map_mul, map_pow]
  exact (Ainf' l).mul_mem (key _) ((Ainf' l).pow_mem (Subring.subset_closure (Or.inr rfl)) _)

end EstT

end period_ring_base
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseA

variable {l : ℕ} [Fact l.Prime]

open GroundTheory.PAdicHodge.ACris in
theorem uB_root {ζ : PadicAlgCl l} {m : ℕ} (hm : 0 < m) (hc : m.Coprime l) (hζ : ζ ^ m = 1)
    (h : ζ ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) : PositivityTheory.LocInh.uB l ⟨ζ, h⟩ ∈ Ainf' l := by
  obtain ⟨T, hT, hθT⟩ := exists_teichmuller_rootOfUnity hm hc hζ
  have hζ0 : (ζ : ℂ_[l]) ≠ 0 := by
    intro h0
    have := norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[l]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hx : iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T) = algClToBdR l ζ := by
    apply eq_of_pow_eq_one_of_theta_eq hm
    · rw [← map_pow, ← map_pow, hT, map_one, map_one]
    · rw [← map_pow, hζ, map_one]
    · rw [thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθT, thetaAlgHom_algClToBdR]
    · rw [thetaAlgHom_algClToBdR]; exact hζ0
  have e : aB l T = PositivityTheory.LocInh.uB l ⟨ζ, h⟩ := by
    apply base_ι_inj l
    have e1 : ι l (aB l T) = algebraMap (BdRp l) (BdR l)
        (iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T)) := ι_cB l _
    rw [e1, hx, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.GaloisCommutant.oD_apply]
  rw [← e]
  exact Subring.subset_closure (Or.inl ⟨T, rfl⟩)

theorem uB_mem (c : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) : PositivityTheory.LocInh.uB l c ∈ Ainf' l := by
  obtain ⟨c, hc⟩ := c
  have e : (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra =
      Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  have adj : ∀ x, x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} →
      x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := fun x hx => by
    have : x ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := e ▸ hx
    exact this
  have key : ∀ x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1},
      ∀ h : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l, PositivityTheory.LocInh.uB l ⟨x, h⟩ ∈ Ainf' l := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      intro h
      obtain ⟨m, hm, hl, hxm⟩ := hx
      exact uB_root hm (Nat.Coprime.symm (((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl)) hxm h
    | algebraMap r =>
      intro h
      have : (⟨algebraMap ℚ_[l] (PadicAlgCl l) r, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) =
          algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) r := rfl
      rw [this, PositivityTheory.LocInh.uB_algebraMap, ← qB_eq]
      exact EstT.qB_mem_ainf r
    | add x y hx hy ihx ihy =>
      intro h
      have : (⟨x + y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ + ⟨y, adj y hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact Subring.add_mem _ (ihx (adj x hx)) (ihy (adj y hy))
    | mul x y hx hy ihx ihy =>
      intro h
      have : (⟨x * y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ * ⟨y, adj y hy⟩ := rfl
      rw [this, map_mul]
      exact Subring.mul_mem _ (ihx (adj x hx)) (ihy (adj y hy))
  exact key c (by have : c ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := hc; rwa [e] at this) hc

end BaseA

open BaseA

theorem base_fixed' (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L →
    ∃ (f : ℕ) (b : Fin f → B l),
    (∀ i, b i ∈ Ainf' l ∧ ∀ σ ∈ L.fixingSubgroup, σB σ (b i) = b i) ∧
    ∀ x, (∀ σ ∈ L.fixingSubgroup, σB σ x = x) → ∃ q : Fin f → ℚ_[l], x = ∑ i, qB l (q i) * b i := by
  intro L hL
  let L0 : IntermediateField ℚ_[l] (PadicAlgCl l) := L ⊓ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l
  have : FiniteDimensional ℚ_[l] L0 := by
    have : FiniteDimensional ℚ_[l] L.toSubalgebra.toSubmodule := hL
    exact Submodule.finiteDimensional_of_le (S₂ := L.toSubalgebra.toSubmodule)
      (S₁ := L0.toSubalgebra.toSubmodule) fun x hx => (IntermediateField.mem_inf.1 hx).1
  let bas := Module.finBasis ℚ_[l] L0
  let c : Fin (Module.finrank ℚ_[l] L0) → ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) :=
    fun i => ⟨(bas i : PadicAlgCl l), (IntermediateField.mem_inf.1 (bas i).2).2⟩
  refine ⟨_, fun i => PositivityTheory.LocInh.uB l (c i), fun i => ⟨uB_mem _, fun σ hσ => ?_⟩, fun x hx => ?_⟩
  · apply base_ι_inj l
    rw [base_ι_σ, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.σD_oD]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.mem_inf.1 (bas i).2).1
  · obtain ⟨k, hkL, hk⟩ := PositivityTheory.LocInh.invB ⟨L, hL⟩ x fun g hg => hx g hg
    let k0 : L0 := ⟨k, IntermediateField.mem_inf.2 ⟨hkL, k.2⟩⟩
    refine ⟨fun i => bas.repr k0 i, ?_⟩
    rw [← hk]
    have hsum := congrArg (fun y : L0 => (y : PadicAlgCl l)) (bas.sum_repr k0).symm
    have hk' : k = ∑ i, algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) (bas.repr k0 i) * c i := by
      apply Subtype.ext
      refine hsum.trans ?_
      simp only [IntermediateField.coe_sum, Algebra.smul_def, IntermediateField.coe_mul, c]
      rfl

    rw [hk', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, PositivityTheory.LocInh.uB_algebraMap, qB_eq]

end period_ring_base
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base

section

@[expose] public section

noncomputable section

namespace period_ring_base

theorem base : PeriodRingBase := fun l _ =>
  { dom := base_dom l
    ι_inj := base_ι_inj l
    σ_one := base_σ_one l
    σ_mul := base_σ_mul l
    σD_one := base_σD_one l
    σD_mul := base_σD_mul l
    σC_one := base_σC_one l
    σC_mul := base_σC_mul l
    φ_σ := base_φ_σ l
    ι_σ := base_ι_σ l
    φ_q := base_φ_q l
    σ_q := base_σ_q l
    ι_q := base_ι_q l
    ι_t := period_image_eq l
    t_unit := base_t_unit l
    frobenius_period := frobenius_period_holds l
    galois_t_transform := galois_period_cyclotomic l
    σ_u := base_σ_u l
    κ_mul := base_κ_mul l
    κ_cont := base_κ_cont l
    χ_cont := base_χ_cont l
    ι_Bst := base_ι_Bst l
    u_Bst := base_u_Bst l
    plus_σ := base_plus_σ l
    th_σ := base_th_σ l
    th_add := base_th_add l
    th_mul := base_th_mul l
    th_q := base_th_q l
    th_zero := base_th_zero l
    t_plus := base_t_plus l
    val := base_val l
    orbit := base_orbit l
    fs_ker := base_fs_ker l
    fs_surj := base_fs_surj l
    ainf_φ := base_ainf_φ l
    ainf_σ := base_ainf_σ l
    ainf_plus := base_ainf_plus l
    ainf_eig := base_ainf_eig l
    fixed := base_fixed' l
    no_kummer := base_no_kummer l }

end period_ring_base
end
end
end
