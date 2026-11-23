module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightKDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.MeasurableConjugateCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.NonDeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.HermitianFormStandardFrameVanishes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SatSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.CongruenceLiftOfBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.MemSecondProjectionIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OmMeas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SplitB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.TransitiveOverLocalRings
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalLatticeOfGlobal

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.LocMassTypW

def LatOfGlob : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E)),
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    LocMassOrdW.IsLatLoc v Λ

end PI.LocMassTypW

namespace PI.LocMassTypL

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

theorem ratV_add (x y : Fin n → E) : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV, map_add (f := _)]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i; simp [ratV]

theorem ratV_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    ratV (F := F) R (∑ i ∈ s, x i) = ∑ i ∈ s, ratV (F := F) R (x i) := by
  funext j; simp [ratV, map_sum, Finset.sum_apply]

theorem ratV_zsmul (m : ℤ) (x : Fin n → E) : ratV (F := F) R (m • x) = m • ratV (F := F) R x := by
  funext i; simp [ratV, map_zsmul]

theorem ratV_smul (a : E) (x : Fin n → E) :
    ratV (F := F) R (a • x) = inclR (F := F) R a • ratV (F := F) R x := by
  funext i; simp [ratV, map_mul]

end Rat

theorem local_lattice_of_global : PI.LocMassTypW.LatOfGlob := by
  intro F E _ _ _ _ _ v n Λ hL
  obtain ⟨L, hL, hLΛ⟩ := hL
  classical
  obtain ⟨S, hS⟩ := hL.toIsLattice.fg
  let b := NumberField.RingOfIntegers.basis E
  set T : Set (Fin n → E) := Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × S =>
    (b p.1 : 𝓞 E) • (p.2 : Fin n → E)) with hT
  have hTfin : T.Finite := Set.finite_range _
  have hTL : T ⊆ (L : Set (Fin n → E)) := by
    rintro _ ⟨⟨j, s⟩, rfl⟩
    exact L.smul_mem _ (hS ▸ Submodule.subset_span (Finset.mem_coe.2 s.2))
  have key : ∀ x ∈ L, ratV (F := F) (Fv F v) x ∈
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).1 hx
    rw [ratV_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    rw [← b.sum_repr (f s), Finset.sum_smul, ratV_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_assoc, ratV_zsmul]
    have hmem : ratV (F := F) (Fv F v) ((b j : 𝓞 E) • s) ∈ ratV (F := F) (Fv F v) '' T :=
      ⟨_, ⟨(j, ⟨s, hs⟩), rfl⟩, rfl⟩
    exact zsmul_mem (Submodule.subset_span hmem) _
  have heq : latLoc (E := E) v Λ =
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    apply le_antisymm
    · rw [latLoc, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hLΛ] at hx
      exact key x hx
    · rw [latLoc]
      exact Submodule.span_mono (Set.image_mono (by rw [← hLΛ]; exact hTL))
  refine ⟨?_, ?_⟩
  · rw [heq]; exact Submodule.fg_span (hTfin.image _)
  · have hspan : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        ratV (F := F) (Fv F v) x ∈ Submodule.span (Fv F v ⊗[F] E)
          (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        show ratV (F := F) (Fv F v) y ∈ latLoc (E := E) v Λ
        exact Submodule.subset_span ⟨y, hLΛ ▸ hy, rfl⟩
      | zero => rw [ratV_zero]; exact Submodule.zero_mem _
      | add y z _ _ h1 h2 => rw [ratV_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h => rw [ratV_smul]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hspan (fun j => if i = j then (1 : E) else 0) (by simp [hL.span_eq_top])
    convert this using 1
    funext j
    by_cases hij : i = j <;> simp [ratV, hij]

end PI.LocMassTypL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxTop

section

@[expose] public section

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

theorem congruence_subgroup_measurable : CongruenceSubgroupMeasurable := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp
  obtain ⟨-, -, hSD, -, hg, -⟩ := hyp
  exact (PI.LocMassTypM.isClosed_congruence_subgroup σ J v Λ hSD hg P).measurableSet

theorem isOpen_uog {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r g : ℕ) : IsOpen (UOg (E := E) v g r) := by
  rw [PI.LocMassTypU.uog_eq v g r]
  exact PI.LocMassTypU.isOpen_boxS _

theorem unipotent_orbit_measurable : MeasUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI := PI.LocMassTypM.borel_tensV (E := E) v
  exact (isOpen_uog (E := E) v r g).measurableSet

theorem unipotent_orbit_count : CountUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI : SecondCountableTopology (UIdx r → Fv F v ⊗[F] E) := inferInstance
  have hB : IsOpen (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := isOpen_uog v r g
  rw [← Set.countable_univ_iff]
  have hd : (Set.univ : Set ((UIdx r → Fv F v ⊗[F] E) ⧸ UOgS (E := E) v g r)).PairwiseDisjoint
      (fun q => (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹' {q}) :=
    Set.pairwiseDisjoint_fiber _ _
  refine hd.countable_of_isOpen (fun q _ => ?_) (fun q _ => ?_)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    have e : (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹'
        {(QuotientAddGroup.mk x : _ ⧸ UOgS (E := E) v g r)} =
        (fun w => -x + w) ⁻¹' (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [e]
    exact hB.preimage (continuous_const.add continuous_id)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨x, rfl⟩

theorem index_formula_of_lift (hL : CongruenceSubgroupLift) (hU : KUnip1) : StepIdx :=
  stepIdx_of hL hU congruence_subgroup_measurable unipotent_orbit_measurable unipotent_orbit_count

end PI.LocMassTypW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IndexFormulaOfSplit

section

@[expose] public section

namespace PI.LocMassTypL

open PI.LocMassTypW

theorem index_formula_of_split (hS : SplitR) (hU : KUnip1) : StepIdx :=
  index_formula_of_lift (congruence_lift_of_split hS) hU

end PI.LocMassTypL
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OrbitMeasure

section

@[expose] public section

noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

theorem orbit_measure : OmMeas := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hyp
  obtain ⟨-, -, -, hSD, -, hg, hgv, -⟩ := hyp
  have hKv : IsClosed (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdKv.isClosed_Kv σ J v Λ hSD
  have hK1 : IsClosed (K1 σ J v Λ g P) := isClosed_congruence_subgroup σ J v Λ hSD hg P

  have hK1' : ∀ k : HA (Fv F v) σ J, IsClosed {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P} := fun k =>
    hK1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  exact ⟨measurableSet_omTyp v Λ σ J hSD hg hgv r, LocMassOrdKv.kv_measurableSet σ J v Λ hSD,
    hK1.measurableSet, measurableSet_image_closed σ J v hKv _,
    fun k => measurableSet_image_closed σ J v (hK1' k) _⟩

end PI.LocMassTypM
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalMassTypeOfParts

section

@[expose] public section

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def StepCT : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E)) (T : F)
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)),
    LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 → P.IsStd σ J T → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g →
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 →
    μS (KSv σ J v P Λ) = μS0 (stabilizerCompact σ J v Λ P) * sdE (E := E) ψ v (UIdx r) (UO v r)

theorem stepCT_of (hKU : KUnip1) : StepCT := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P))) := by
    have := Fr.2.2.2.2.2.2.2.2.2
    rwa [one_smul] at this
  have key := LocMassOrdSC.stepC_at σ J ψ v P Λ μG μS μS0 1 Fr
    (LocMassOrdSC.measConj σ J v Λ Fr.2.2.1 1) (LocMassOrdSC.measurable_unipotent_orbit v r)
    (unipSplitF PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      σ J ψ v P Λ T Fr.1 hP Fr.2.2.1 Fr.2.2.2.1 hEta hL hPr)
    (fun x hx => by
      obtain ⟨s, hs, hsx⟩ := hKU σ J ψ v g P Λ T μS0
        ⟨Fr.1, hP, Fr.2.2.1, Fr.2.2.2.1, hg, hgv, hN, hEta, hPr, hL, Fr.2.2.2.2.2.2.1, ha⟩ x hx
      exact ⟨s, hsx, by simpa using hs⟩)
  rwa [KSv_eq, stabilizer_compact_eq] at key

theorem local_mass_type_formula (hOm : StepOm) (hC : StepCT) (hIdx : StepIdx) (hG : LatOfGlob)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ := by
  intro hStd T T' hP hP' hSD hUn hGL hg hgv hN hEta hκ μG hμG μS hμS hTie μS' hμS' hTie' hPr hPr'
  have hL := hG v Λ hGL
  obtain ⟨κ, hκK, hκc⟩ := hκ
  obtain ⟨μS0, hμS0, hCm, hPU⟩ := hTie
  obtain ⟨μS0', hμS0', hCm', hPU'⟩ := hTie'
  have Fr : LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 :=
    ⟨hStd, ⟨T, hP⟩, hSD, hUn, hμG, hμS, hμS0, hCm, hPU, by rw [one_smul]; exact hPr⟩
  have Fr' : LocMassOrdW.FrameHyp σ J ψ v P' Λ μG μS' μS0' 1 :=
    ⟨hStd, ⟨T', hP'⟩, hSD, hUn, hμG, hμS', hμS0', hCm', hPU', by rw [one_smul]; exact hPr'⟩
  have ha : (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P Λ μG μS μS0 1 Fr hL
  have ha' : (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0 := by
    rw [← stabilizer_compact_eq]; exact LocMassOrdND.nondegenerate_lattice σ J ψ v P' Λ μG μS' μS0' 1 Fr' hL
  have h1 := hC σ J ψ v g P Λ T μG μS μS0 Fr hP hEta hL hg hgv hN ha
  have h2 := hC σ J ψ v g P' Λ T' μG μS' μS0' Fr' hP' hEta hL hg hgv hN ha'
  have h1r := congrArg ENNReal.toReal h1
  have h2r := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_mul] at h1r h2r
  have hu := PI.LocMassTypU.unitary_local_mass_identity σ J ψ v (r := r) g hStd hg hgv
  rw [hu, h1r, h2r]
  have hM := hOm σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκK hκc
    hμG hμS0 hCm hμS0' hCm' hPr hPr' hL ha ha'
  have hi := hIdx σ J ψ v g P Λ T μG μS0 hStd hP hSD hUn hg hgv hN hEta hPr hμG hL hμS0 ha
  exact arith _ _ _ _ _ _ _ _ _ _ hM rfl rfl hi ha ha' (PI.LocMassTypU.positivity_of_local_mass σ J ψ v g hStd hg hgv)

theorem local_mass_type_of_parts (hRK : RightK) (hKU : KUnip1)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) :
    Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  local_mass_type_formula
    (stepOm_ofK (stepW_of PI.LocMassTypS.split_reduction (PI.LocMassTypL.latStd_of PI.LocMassTypS.split_reduction)
      saturated_split_lattice transitiveOverLocalRings) PI.LocMassTypM.orbit_measure hRK LocMassOrdSF.orbit_measure_sFinite)
    (stepCT_of hKU) (PI.LocMassTypL.index_formula_of_split PI.LocMassTypS.split_reduction hKU)
    PI.LocMassTypL.local_lattice_of_global σ J ψ v g P P' Λ

end PI.LocMassTypW
end
end
end
