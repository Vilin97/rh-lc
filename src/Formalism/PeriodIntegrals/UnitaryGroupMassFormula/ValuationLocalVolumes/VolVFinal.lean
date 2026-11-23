module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MemALImage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiagonalOneJacobian
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.GoodTransvection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.Transport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTyp

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AbsVDetBigL

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VolOrdW.absV_one]
  | succ n ih => rw [pow_succ, VolOrdW.absV_mul, ih, pow_succ]

theorem meas_image (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (f : (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E))
    (hf : LinearMap.det f ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) (hS : MeasurableSet S) :
    μ (f '' S) = ENNReal.ofReal (absV v (LinearMap.det f)) * μ S := by
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.locallyCompact_Fv v
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  rw [hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ f hf μ inferInstance S hS,
    PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hf]
  rfl

section Big

variable (r : ℕ)

def famL (g : Fv F v) (θ : Fv F v ⊗[F] E) (p : Fin (r + 1) × Fin (r + 1)) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then g • LinearMap.id else if p.1 = p.2 then aL v g θ else LinearMap.id

def bigL (g : Fv F v) (θ : Fv F v ⊗[F] E) :
    (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  LinearMap.pi fun p => (famL v r g θ p).comp (LinearMap.proj p)

theorem det_famL_mul (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) (p : Fin (r + 1) × Fin (r + 1)) :
    LinearMap.det (famL v r g θ p) * LinearMap.det (famL v r g θ p.swap) = g ^ 2 := by
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have hs : LinearMap.det (g • (LinearMap.id : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E))) = g ^ 2 := by
    rw [LinearMap.det_smul, LinearMap.det_id, hr, mul_one]
  have ha := det_aL v hfin g θ Δ hθ hΔ hΔ0
  obtain ⟨i, j⟩ := p
  simp only [Prod.swap_prod_mk]
  rcases lt_trichotomy i j with h | h | h
  · have h1 : ¬ j < i := not_lt.2 h.le
    have h2 : j ≠ i := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, mul_one]
  · subst h
    simp only [famL, lt_irrefl, if_false, if_true, ha, sq]
  · have h1 : ¬ i < j := not_lt.2 h.le
    have h2 : i ≠ j := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, one_mul]

theorem det_bigL_sq (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (bigL v r g θ) ^ 2 = (g ^ 2) ^ ((r + 1) ^ 2) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [bigL, LinearMap.det_pi, sq]
  have e : ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p.swap) =
      ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  conv_lhs => arg 2; rw [← e]
  rw [← Finset.prod_mul_distrib]
  simp only [det_famL_mul v r hfin g θ Δ hθ hΔ hΔ0, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, sq]

theorem absV_det_bigL (hfin : Module.finrank F E = 2) {g : ℕ} (hg0 : g ≠ 0)
    (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) :
    LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 ∧
      absV v (LinearMap.det (bigL v r (g : Fv F v) θ)) = (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  have h2 := det_bigL_sq v r hfin (g : Fv F v) θ Δ hθ hΔ hΔ0
  have hD : LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at h2
    exact (pow_ne_zero _ (pow_ne_zero _ hgv)) h2.symm
  refine ⟨hD, ?_⟩
  have h3 := congrArg (absV v) h2
  rw [absV_pow, absV_pow, absV_pow, hg] at h3
  have hpos := (VolOrdW.absV_pos v hD).le
  have hgpos : (0 : ℝ) ≤ (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by positivity
  refine (pow_left_inj₀ hpos hgpos two_ne_zero).1 ?_
  rw [h3, ← pow_mul, ← pow_mul, mul_comm]

end Big

end Formalism.L2.SG.Pf.NcVal.VolV
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ThetaExists

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

section Box

variable (r : ℕ)

def pSet (g : ℕ) (p : Fin (r + 1) × Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then {y | y * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else if p.1 = p.2 then
    {y | y ∈ OEv (E := E) v ∧ (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}
  else OEv (E := E) v

theorem famL_image
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (p : Fin (r + 1) × Fin (r + 1)) (y : Fv F v ⊗[F] E) :
    y ∈ famL v r (g : Fv F v) θ p '' OEv (E := E) v ↔ y ∈ pSet σ v r g p := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  unfold famL pSet
  split_ifs with h1 h2
  · simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, ← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        one_mul]
      exact hz
    · intro h
      refine ⟨y * sc (E := E) v (g : Fv F v)⁻¹, h, ?_⟩
      rw [← VolTU.sc_mul_eq_smul, mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ hgv, VolTU.sc_one,
        mul_one]
  · exact mem_aL_image v σ htr hg0 hθO hθ y
  · simp

theorem box_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) :
    μ {Y | ∀ p, Y p ∈ pSet σ v r g p} = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  obtain ⟨hD, hA⟩ := absV_det_bigL v r hfin hg0 hg θ Δ hθ hΔ hΔ0
  have himg : bigL v r (g : Fv F v) θ '' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      {Y | ∀ p, Y p ∈ pSet σ v r g p} := by
    ext Y
    simp only [Set.mem_image, Set.mem_setOf_eq, VolTO]
    constructor
    · rintro ⟨Z, hZ, rfl⟩ p
      exact (famL_image σ v r htr hg0 hθO hθ p _).1 ⟨Z p, hZ p, rfl⟩
    · intro h
      have : ∀ p, ∃ z, z ∈ OEv (E := E) v ∧ famL v r (g : Fv F v) θ p z = Y p := fun p =>
        (famL_image σ v r htr hg0 hθO hθ p _).2 (h p)
      choose Z hZ using this
      exact ⟨Z, fun p => (hZ p).1, funext fun p => (hZ p).2⟩
  have hgpos : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero hg0
  rw [← himg, meas_image v _ μ _ hD _ (VolUL.volTO_meas v _), hK, mul_one, hA,
    ENNReal.ofReal_pow (inv_nonneg.2 hgpos.le), ENNReal.ofReal_inv_of_pos hgpos, ENNReal.ofReal_natCast,
    ENNReal.inv_pow]

theorem diag_key
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {θ : Fv F v ⊗[F] E} (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (c y : Fv F v ⊗[F] E)
    (hc : sigR (Fv F v) σ c = c) :
    (y - c * θ) + sigR (Fv F v) σ (y - c * θ) = y + sigR (Fv F v) σ y - c := by
  have h1 : θ + sigR (Fv F v) σ θ = 1 := by rw [← htr, hθ, map_one]
  rw [map_sub, map_mul, hc]
  linear_combination (-c) * h1

def ctr (θ : Fv F v ⊗[F] E) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (p : Fin (r + 1) × Fin (r + 1)) : Fv F v ⊗[F] E :=
  if p.1 < p.2 then c p.1 p.2 else if p.1 = p.2 then c p.1 p.2 * θ else 0

theorem hermBox_eq
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    VolUHm.hermBox σ v g r c =
      {Y | (fun p => Y p - ctr v r θ c p) ∈ {Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E |
        ∀ p, Y p ∈ pSet σ v r g p}} := by
  have hgO : sc (E := E) v (g : Fv F v) ∈ OEv (E := E) v := VolUTr.TrW.alg_mem v (VolTU.natCast_memO v g)
  ext Y
  simp only [VolUHm.hermBox, Set.mem_setOf_eq]
  constructor
  · intro h p
    obtain ⟨i, j⟩ := p
    obtain ⟨hO, hup, hdg⟩ := h i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq]
      exact hup hij
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq]
      refine ⟨Submodule.sub_mem _ hO (VolUTr.TrW.mul_mem v (hc.2 i i) hθO), ?_⟩
      rw [diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hdg rfl
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero]
      exact hO
  · intro h i j
    have hp := h (i, j)
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [ctr, pSet, if_pos hij, Set.mem_setOf_eq] at hp
      have hO : Y (i, j) ∈ OEv (E := E) v := by
        have e : Y (i, j) = sc (E := E) v (g : Fv F v) * ((Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹) +
            c i j := by
          rw [mul_comm, mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (VolTU.natCast_ne_zero v hg0), VolTU.sc_one,
            mul_one, sub_add_cancel]
        rw [e]
        exact Submodule.add_mem _ (VolUTr.TrW.mul_mem v hgO hp) (hc.2 i j)
      exact ⟨hO, fun _ => hp, fun h => absurd h hij.ne⟩
    · subst hij
      simp only [ctr, pSet, lt_irrefl, if_false, if_true, Set.mem_setOf_eq] at hp
      have hO : Y (i, i) ∈ OEv (E := E) v := by
        rw [← sub_add_cancel (Y (i, i)) (c i i * θ)]
        exact Submodule.add_mem _ hp.1 (VolUTr.TrW.mul_mem v (hc.2 i i) hθO)
      refine ⟨hO, fun h => absurd h (lt_irrefl _), fun _ => ?_⟩
      rw [← diag_key σ v htr hθ _ _ (hc.1 i i).symm]
      exact hp.2
    · have h1 : ¬ i < j := not_lt.2 hij.le
      have h2 : i ≠ j := hij.ne'
      simp only [ctr, pSet, if_neg h1, if_neg h2, sub_zero] at hp
      exact ⟨hp, fun h => absurd h h1, fun h => absurd h h2⟩

theorem hermBox_meas (hfin : Module.finrank F E = 2)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) {θ Δ : Fv F v ⊗[F] E}
    (hθO : θ ∈ OEv (E := E) v) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1)
    (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0) (hΔ0 : Δ ≠ 0)
    (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolUHm.hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹ := by
  rw [hermBox_eq σ v r htr hg0 hθO hθ c hc, VolUH.sub_pre v _ μ,
    box_meas σ v r hfin htr hg0 hg hθO hθ hΔ hΔ0 μ hK]

end Box

theorem theta_exists (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x) (hfin : Module.finrank F E = 2)
    (a t : 𝓞 E) (ht : σ (a : E) = (t : E)) (e : 𝓞 F)
    (he : ((a : E) - t) ^ 2 = algebraMap F E (e : F)) (hev : e ∉ v.asIdeal) :
    ∃ θ Δ : Fv F v ⊗[F] E, θ ∈ OEv (E := E) v ∧ Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1 ∧
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0 ∧ Δ ≠ 0 := by
  have hst : σ (t : E) = a := by rw [← ht, hinv]
  have hTa : Algebra.trace F E ((a : E) - t) = 0 := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_sub, ht, hst, map_zero]
    ring
  have hTb : Algebra.trace F E ((a : E) * ((a : E) - t)) = e := by
    apply (algebraMap F E).injective
    rw [VolUTr.TrW.trace_eq_add σ hinv hnt hfin, map_mul, map_sub, ht, hst, ← he]
    ring
  set ev := algebraMap F (Fv F v) (e : F) with hevdef
  have hval : Valued.v ev = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F e)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hev] at h
    exact h
  have he0 : ev ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hinvm : ev⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hθ1 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
      (sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t))) = 1 := by
    rw [VolUTr.TrW.sc_eq, ← Algebra.smul_def, map_smul, PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTb, smul_eq_mul,
      inv_mul_cancel₀ he0]
  refine ⟨sc (E := E) v ev⁻¹ * inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)),
    inclR (F := F) (Fv F v) ((a : E) - t), ?_, hθ1, ?_, ?_⟩
  · refine VolUTr.TrW.mul_mem v (VolUTr.TrW.alg_mem v hinvm) ?_
    have e1 : (((a * (a - t) : 𝓞 E)) : E) = (a : E) * ((a : E) - t) := by push_cast; ring
    rw [← e1]
    exact VolUTr.TrW.inclR_mem' (E := E) v (a * (a - t))
  · rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR, hTa, map_zero]
  · intro h0
    rw [show inclR (F := F) (Fv F v) ((a : E) * ((a : E) - t)) =
        inclR (F := F) (Fv F v) (a : E) * inclR (F := F) (Fv F v) ((a : E) - t) from map_mul _ _ _, h0,
      mul_zero, mul_zero, map_zero] at hθ1
    exact zero_ne_one hθ1

end Formalism.L2.SG.Pf.NcVal.VolV
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHermBoxHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volUHermBox_holds {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) : VolUHermBox X ψ := by
  intro hψ hs v hv
  obtain ⟨hg, -, hd⟩ := VolUT.typ_arith X v hv
  have hann := VolUTr.annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v
  have hfin := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  haveI := hH
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
      exact bot_le)
  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  set σ := X.B.I.cm.sig with hσ
  have hσx : ∀ x, σ x = star x := fun x => rfl
  have hinv : ∀ y, σ (σ y) = y := fun y => by rw [hσx, hσx, star_star]
  have ht : σ (θ : X.B.I.E) = (t : X.B.I.E) := by rw [hσx]; exact htθ.symm
  have hne : (θ : X.B.I.E) ≠ t := by
    intro h
    apply hnot
    have : θ - t = 0 := by ext; simp [h]
    rw [this]; exact P.zero_mem
  have hnt : ∃ x, σ x ≠ x := ⟨θ, by rw [ht]; exact fun h => hne h.symm⟩
  have hfix : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2 := by
    have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
    have h1 : star (t : X.B.I.E) = θ := by rw [htθ', star_star]
    rw [star_pow, star_sub, h1, ← htθ']
    ring
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed _).1 hfix
  have hint : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E f) := by
    rw [hf]
    have h1 : (((θ - t) ^ 2 : 𝓞 X.B.I.E) : X.B.I.E) = ((θ : X.B.I.E) - t) ^ 2 := by push_cast; ring
    rw [← h1]
    exact RingOfIntegers.isIntegral_coe _
  have hfint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)
      (algebraMap X.B.I.F X.B.I.E).injective).mp hint
  set e : 𝓞 X.B.I.F := ⟨f, hfint⟩ with he
  have he2 : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F) := hf.symm
  have hev : e ∉ v.asIdeal := by
    intro hm
    rw [← hPv] at hm
    have hm' : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e ∈ P := hm
    have heq : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2 := by
      apply RingOfIntegers.coe_injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, map_pow, map_sub]
      exact he2.symm
    rw [heq] at hm'
    exact hnot (hPmax.isPrime.mem_of_pow_mem 2 hm')
  obtain ⟨θ0, Δ, hθO, hθ, hΔ, hΔ0⟩ := VolV.theta_exists σ v hinv hnt hfin θ t ht e he2 hev
  have htr := VolUTr.TrW.trace_v v σ hinv hnt hfin
  intro c hc
  exact VolV.hermBox_meas σ v _ hfin htr (gAt_prime X v).ne_zero hg hθO hθ hΔ hΔ0 _ hO c hc

end Formalism.L2.SG.Pf.NcVal
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volTypV_holds {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) :
    VolTypV X u u' ψ :=
  volTypV_of_box X u u' ψ (volUHermBox_holds X ψ)

end Formalism.L2.SG.Pf.NcVal
end
end
end
