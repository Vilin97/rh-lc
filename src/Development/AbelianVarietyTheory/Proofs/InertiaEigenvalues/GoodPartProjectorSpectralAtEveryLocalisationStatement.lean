module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.TypeOrthClassSum

theorem typeOrth_of_classSum : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  intro D M V i hC
  obtain ⟨hbd, β, T, c, hβ, hT, hc, hin⟩ := hC
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson D.host.E D.R.nV (M.loc i).wt β hβ
  obtain ⟨c', hc', hcc⟩ := hBc (M.loc i).J (M.loc i).χ T hbd (M.loc i).J_open hT
  have hreal : ∀ x, (M.loc i).real x ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := fun x => by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ x
  set r : ℝ := c * c' with hr
  have hr0 : 0 < r := mul_pos hc hc'
  have hsmul : ∀ f f', (((r : ℂ) • B) f f') = (r : ℂ) * B f f' := fun f f' => by
    simp [LinearMap.smul_apply]

  have hcls : ∃ T' : Finset (GAf D.host.E D.R.nV), ∀ g : GAf D.host.E D.R.nV, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV)
      (t : GAf D.host.E D.R.nV) (u : GAf D.host.E D.R.nV), t ∈ T' ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV ∧
      g = (γ : GAf D.host.E D.R.nV) * t * u := by
    classical
    obtain ⟨F, hF⟩ := hbd
    refine ⟨(T ×ˢ F).image (fun p => p.1 * p.2), fun g => ?_⟩
    obtain ⟨t, ⟨htT, γ, κ, hκ, hg⟩, -⟩ := hT g
    obtain ⟨f, hfF, hu⟩ := hF κ hκ
    refine ⟨γ, t * f, f⁻¹ * κ, Finset.mem_image.2 ⟨(t, f), Finset.mem_product.2 ⟨htT, hfF⟩, rfl⟩, hu, ?_⟩
    rw [hg]; group
  have key := GlobalTheory.ThetaExh.typeOrth_of_avTied D M V i ((r : ℂ) • B) ?_ ?_ ?_
  · exact key
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, fun hne => ?_, fun h => ?_⟩
    · rw [hsmul, hsmul, h1, map_mul, Complex.conj_ofReal]
    · rw [hsmul, Complex.re_ofReal_mul]; exact mul_pos hr0 (h2 hne)
    · rw [hsmul, hsmul, h3]
  · intro x y
    rw [hin, hsmul, hcc _ (hreal x) _ (hreal y), hr]
    push_cast; ring
  · intro N hN
    exact GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (M.loc i).wt hcls N hN

end GlobalTheory.TypeOrthClassSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLowerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  first | exact @GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | exact GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | (intros; apply GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecPrOfZSpecTypeTie

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin.SpecProj

theorem le_iSup_of_dichotomy {V ι : Type} [AddCommGroup V] [Module ℂ V] (T : ι → Submodule ℂ V) (A B : Submodule ℂ V)
    (hd : Disjoint A B) (ht : ⨆ P, T P = ⊤) (h : ∀ P, T P ≤ A ∨ T P ≤ B) : A ≤ ⨆ P ∈ {P | T P ≤ A}, T P := by
  intro x hx
  have hle : (⊤ : Submodule ℂ V) ≤ (⨆ P ∈ {P | T P ≤ A}, T P) ⊔ B := by
    rw [← ht]
    refine iSup_le fun P => (h P).elim (fun hP => le_sup_of_le_left ?_) le_sup_of_le_right
    exact le_biSup T (show P ∈ {P | T P ≤ A} from hP)
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle (Submodule.mem_top (x := x)))
  have ha' : a ∈ A := (iSup₂_le fun P hP => hP : (⨆ P ∈ {P | T P ≤ A}, T P) ≤ A) ha
  have hb0 : b = 0 := Submodule.disjoint_def.1 hd b (by rw [← add_sub_cancel_left a b, e]; exact A.sub_mem hx ha') hb
  rw [← e, hb0, add_zero]; exact ha

theorem specPr_of_zSpec_typeTie : ∀ (D : D7) (i : D.nd.Loc), ZSpec D i → TypeTie D i → SpecPr D i := by
  intro D i hZ hT
  have hd := (Idx.Z0 D (D.nd.mu i) (D.nd.j i)).orthogonal_disjoint
  have mono : ∀ {Y Y' : Set (D.nd.X i)}, Y ⊆ Y' → D.nd.eigSum i Y ≤ D.nd.eigSum i Y' := fun h => biSup_mono h
  constructor
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd (D.naut.typeV_top i) (fun P => (hZ P).1) hy))
    rintro x ⟨P, hP, hx⟩
    by_contra hn
    exact D.naut.typeV_ne i P (hd hP (((hZ P).2 x hx).2 hn) |> le_bot_iff.1)
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd.symm (D.naut.typeV_top i) (fun P => (hZ P).1.symm) hy))
    rintro x ⟨P, hP, hx⟩ hn
    exact D.naut.typeV_ne i P (hd (((hZ P).2 x hx).1 hn) hP |> le_bot_iff.1)

end GlobalTheory.EtaJoin.SpecProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.typeSpace_projection_to_pointEigenspaces : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  first | exact @GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | exact GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | (intros; apply GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisation

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower D M AV i (CS i)) (TC i) II PZ
      (GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := GlobalTheory.T.typeSpace_projection_to_pointEigenspaces D M i HT HR AV SU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.good_part_projector_spectral_at_every_localisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  first | exact @GlobalTheory.EtaJoin.SpecAll.specPr_all | exact GlobalTheory.EtaJoin.SpecAll.specPr_all | (intros; apply GlobalTheory.EtaJoin.SpecAll.specPr_all <;> assumption)
end
end
