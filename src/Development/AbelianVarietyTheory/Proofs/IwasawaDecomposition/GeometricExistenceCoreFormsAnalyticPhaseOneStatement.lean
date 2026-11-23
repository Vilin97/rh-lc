module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuplesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharacters
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharactersStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_core_compatible_adelicData_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_tieIn_reCore | exact GlobalTheory.RealGeo.exists_tieIn_reCore | (intros; apply GlobalTheory.RealGeo.exists_tieIn_reCore <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariantStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_core_constants_base_solution_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  first | exact @GlobalTheory.RealGeoConst.exists_constants | exact GlobalTheory.RealGeoConst.exists_constants | (intros; apply GlobalTheory.RealGeoConst.exists_constants <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricActionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_geometric_half_realisation_geometric_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  first | exact @GlobalTheory.RealGeo.exists_geoHalf_geoR | exact GlobalTheory.RealGeo.exists_geoHalf_geoR | (intros; apply GlobalTheory.RealGeo.exists_geoHalf_geoR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDatStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_referenceTuple_thetaComparison_normalisedData : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → Formalism.L2.Host.ValLL D R.C → TieIn T R κ v₀ → T.pb = R.C.P.pb → QGuard R → (∀ i, VStd D i) → ∃ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ i, OMPins T R κ v₀ O i := by
  first | exact @GlobalTheory.RefPins.exists_omPins | exact GlobalTheory.RefPins.exists_omPins | (intros; apply GlobalTheory.RefPins.exists_omPins <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  first | exact @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral | exact GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral | (intros; apply GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicForms

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo



theorem omDat_updFW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ nW FW i Tp tup O
  refine ⟨{ O with }, rfl, rfl, fun h => ?_, fun cc ph h => h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end GlobalTheory.RealGeo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  first | exact @GlobalTheory.RealGeo.omDat_updFW | exact GlobalTheory.RealGeo.omDat_updFW | (intros; apply GlobalTheory.RealGeo.omDat_updFW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoHalfTop

theorem exists_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  intro hC D G _ _ Pl0 T0 A T _ R hvol hJ hcore halg hpb hpre hval hfr hLL hfin hQ hstd hn
  obtain ⟨dict, mu, chiW, x₀, htie, hcore₁⟩ := GlobalTheory.T.exists_core_compatible_adelicData_characters D G Pl0 T0 A T R hvol hJ hcore halg hpre.lev hval hfr
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hpre.lev hpre.fam hpre.models hpre.thP
  obtain ⟨O, hO⟩ := GlobalTheory.T.exists_referenceTuple_thetaComparison_normalisedData D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) hpre hLL htie hpb hQ hstd
  choose cc hcc0 hcc using fun i => GlobalTheory.T.exists_constants_theta_comparison_all_tuples D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O hpre htie
    hpb hfin hQ hio i (hstd i) (hO i)
  obtain ⟨cE, hcE, htie₂, hO₂, hF⟩ := GlobalTheory.T.exists_core_constants_base_solution_equivariant D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O cc
    hpre.lev htie hpb hO hcc0
  obtain ⟨B, hκ, hv, hFB, hpre₂, hchi⟩ := GlobalTheory.T.exists_geometric_half_realisation_geometric_action D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O
    (fun _ => 1) hpre htie₂ hO₂ hF
  obtain ⟨hin, hU, hI⟩ := GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral hC D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) _ (fun _ => 1) B hpre₂ hchi hpb hn
  refine ⟨dict, mu, chiW, x₀, cE, _, _, B, hκ, hin, hFB, fun i => ⟨⟨_, _, hFB.1 i⟩, fun _ => ?_⟩,
    GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ _ hpre₂.lev hpre₂.fam hpre₂.models hpre₂.thP, hpre₂, hchi, hU, hI, hcore₁⟩
  obtain ⟨O', h1, h2, h3⟩ := hcc i
  obtain ⟨O'', e1, -, p1, p2⟩ := GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R)
    (nTop (reCore T dict mu chiW x₀ cE) (kapTop D)) (formsGeo (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O) i T0 id O'
  rw [hκ, hv]
  refine ⟨O'', ?_, p1 h2, ?_⟩
  · rw [e1]; exact h1
  · rw [← hcE i] at h3
    exact p2 _ _ h3

end GlobalTheory.GeoHalfTop

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCoreStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  first | exact @GlobalTheory.GeoHalfTop.exists_geoHalf | exact GlobalTheory.GeoHalfTop.exists_geoHalf | (intros; apply GlobalTheory.GeoHalfTop.exists_geoHalf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.GeoExProof



theorem geoExV_of_top : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  intro hRD D G _ _ Pl0 I0 T0 A3 C _ F hVol hL hLC hA hT hVS hn R cG hVal hPre _hlev hpb hK
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, B, -, -, hFired, -, -, hPre', hchi, hU, -, -⟩ :=
    GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core hRD D G Pl0 T0 A3.A C R hVol hL hLC hA hpb hPre hK.valKs hK.frameKs hVal hT hK.guard hVS hn
  refine ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨B⟩, fun i x => ?_⟩
  have hHW := hPre'.models.HW
  obtain ⟨m, a, f, hf⟩ := (hFired.1 i).2.2 x
  have hm : (1 : ℂ) • ((updFW R nW FW).HW i (sg0 D A3.A)).e (R.thG i A3.A.μ0 (jVx (updFW R nW FW) i A3.A.μ0 x)) ∈
      (updFW R nW FW).Wall i (sg0 D A3.A) :=
    ((updFW R nW FW).Wall i (sg0 D A3.A)).smul_mem 1 ((hHW i _).2.1.le (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := GlobalTheory.TwistedClassSum.exists_adForm B.fw hHW hU (B.O i).hV hm a f 1 fun q =>
    (hf q.out).trans (one_mul _).symm
  rw [one_smul, one_smul] at hy
  exact ⟨y, (hHW i _).1 hy.symm⟩

end GlobalTheory.Mem.R3.GeoExProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  first | exact @GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | exact GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | (intros; apply GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top <;> assumption)
end
end
