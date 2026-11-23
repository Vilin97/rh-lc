module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixMulKer
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.AddMemIffOfZero

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNormStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_local_approximate_identity : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (AF F), IsCovolOne db → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → Ainf F → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : Fv F v) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : Fv F v)).smallSets) ∧ (∀ k, Integrable (Coef.fouA ψ db (Coef.testT (ρ k) S (U k))) db ∧ ∀ z, ∫ b, Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b * ψ (b * z) ∂db = Coef.testT (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, Coef.testT (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * ∏ v ∈ S, (((lam v) (U k v)).toReal : ℂ)) ∧ (∀ k b, ‖Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b‖ ≤ ‖∫ y, Coef.testT (ρ k) S (U k) y ∂db‖) ∧ ∀ b, Filter.Tendsto (fun k => Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b / ∫ y, Coef.testT (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((Coef.intF S).indicator (fun _ => (1 : ℂ)) (sndA F b))) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_adelic_haar_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ db : Measure (AF F), IsCovolOne db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open scoped RestrictedProduct

theorem rp_nhds {ι : Type} {R : ι → Type} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (hA : ∀ i, IsOpen (A i)) (x : ∀ i, A i) (W : Set (Πʳ i, [R i, A i]))
    (hW : W ∈ 𝓝 (RestrictedProduct.structureMap R A cofinite x)) :
    ∃ V : ∀ i, Set (R i), (∀ i, V i ∈ 𝓝 (x i : R i)) ∧ ∀ z : Πʳ i, [R i, A i], (∀ i, z i ∈ V i) → z ∈ W := by
  rw [RestrictedProduct.nhds_eq_map_structureMap hA, Filter.mem_map, nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have ht' : ∀ i, ∃ u ∈ 𝓝 (x i : R i), Subtype.val ⁻¹' u ⊆ t i := fun i => mem_nhds_subtype _ _ _ |>.1 (ht i)
  choose u hu hut using ht'
  refine ⟨fun i => u i ∩ A i, fun i => Filter.inter_mem (hu i) ((hA i).mem_nhds (x i).2), fun z hz => ?_⟩
  let y : ∀ i, A i := fun i => ⟨z i, (hz i).2⟩
  have hyz : RestrictedProduct.structureMap R A cofinite y = z := Subtype.ext rfl
  rw [← hyz]
  exact hIt fun i _ => hut i (hz i).1

theorem af_nhds {F : Type} [Field F] [NumberField F] (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, V v ∈ 𝓝 (0 : Fv F v)) ∧
      ∀ z : Af F, (∀ v, z v ∈ V v) → z ∈ W := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => Valued.isOpen_valuationSubring _
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun _ => ⟨0, zero_mem _⟩) =
      (0 : Af F) := rfl
  rw [← h0] at hW
  exact rp_nhds hA _ W hW

theorem top1 {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsIdF S ε)
    (A : ℕ → Set (Ainf F)) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hA : Tendsto A atTop (𝓝 0).smallSets) (hU : ∀ v, Tendsto (fun k => U k v) atTop (𝓝 0).smallSets) :
    Tendsto (fun k => {a : AF F | ε * a = a ∧ fstA F a ∈ A k ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}) atTop
      (𝓝 (0 : AF F)).smallSets := by
  rw [Filter.tendsto_smallSets_iff]
  intro W hW
  obtain ⟨W1, hW1, W2, hW2, hsub⟩ := mem_nhds_prod_iff.1 (show W ∈ 𝓝 ((0, 0) : Ainf F × Af F) from hW)
  obtain ⟨V, hV, hVW⟩ := af_nhds W2 hW2
  have e1 := Filter.tendsto_smallSets_iff.1 hA W1 hW1
  have e2 : ∀ᶠ k in atTop, ∀ v ∈ S, U k v ⊆ V v :=
    (Filter.eventually_all_finset S).2 fun v _ => Filter.tendsto_smallSets_iff.1 (hU v) (V v) (hV v)
  filter_upwards [e1, e2] with k h1 h2
  rintro a ⟨hεa, haA, haU⟩
  apply hsub
  refine ⟨h1 haA, hVW (sndA F a) fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact h2 v hv (haU v hv)
  · have h3 : sndA F a = sndA F ε * sndA F a := by rw [← map_mul, hεa]
    have h4 : (sndA F a) v = (sndA F ε) v * (sndA F a) v := congrArg (fun z : Af F => z v) h3
    rw [hε.2 v, if_neg hv, zero_mul] at h4
    rw [h4]
    exact mem_of_mem_nhds (hV v)

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdB

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

theorem oneD : OneD := by
  intro F _ _ hF ψ hψ S ε hε ν hν
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨db, hdb⟩ := GlobalTheory.T.exists_adelic_haar_covolume_one F
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamex
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_local_approximate_identity F hF ψ hψ db hdb laminf lam hinf hlam
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩ := hS₁ (S ∪ S₁) Finset.subset_union_right
  haveI : db.IsAddHaarMeasure := hdb.1
  have hεε := idF_mul hε
  have hp : Continuous (AddMonoidHom.mulLeft ε) := continuous_const.mul continuous_id
  have hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x := fun x => by
    simp only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]
  have hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F))) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace
  haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (fixE ε) := inferInstance
  haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨c, hc, hdec⟩ := decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0 := by
    intro k
    rw [hint k]
    refine mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    have h1 : 0 < (lam v) (U k v) := (hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩
    have h2 : (lam v) (U k v) ≠ ⊤ := (hU k v).1.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc
    hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)
  refine ⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)),
    fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v},
    fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩,
    fun h => ?_, fun k s hs => ?_, top1 S ε hε _ U hρt hUt⟩
  · have hl := hlim h.1
    have hm : sndA F h.1 ∈ intF (S ∪ S₁) := fun v hv => by
      rw [snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]
      exact zero_mem _
    rw [Set.indicator_of_mem hm] at hl
    simp only [hgeq]
    exact hl
  · have ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0 := fun h0 => hs (by simp only [h0, mul_zero])
    unfold tR at ht
    have hρne : ρ k (fstA F (-(ε * s))) ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
    have hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k) := by
      by_contra hn
      exact ht (by rw [Set.indicator_of_notMem hn, mul_zero])
    exact ⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne,
      fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end
end
