module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricActionCoveringGroupOfCoreEquivarianceStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLeOfAntilinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralZpowOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoActOfTiesOfEquivAll

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory



theorem geoAct_of_ties_of_equivAll : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → EquivAll T R κ O → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hl hi hw ht hpb hp he
  exact GlobalTheory.T.geometricAction_coveringGroup_of_core_equivariance T R κ v₀ O hi hw ht hp fun i σ hσ hV =>
    he i σ hσ hV (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hl ht hpb hp i σ hσ hV)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvInjOfTieIn

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberEvalInj

theorem evInj_of_tieIn : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → EvInj T R v₀ :=
  fun _ _ _ _ _ _ _ T _ R _ v₀ _ hm ht _ => GlobalTheory.EvalAtUnitVector.evInj T R v₀ hm.HW ht.hv₀

end GlobalTheory.MemberEvalInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoIn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}



theorem mkStable_of_rhoGeo (t : FWTie T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) (hr : RhoGeo t O) (i : Fin D.R.m) :
    (R.FW i).MKStable := by
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  by_cases hk : ActKeeps (κ := κ) O i
  · have h0 := (hr i).1 hk
    intro g x
    have key : ∀ hx : x ∈ (R.FW i).WK, (R.FW i).ρ g x ∈ (R.FW i).WK ∧ (x ∈ (R.FW i).MK → (R.FW i).ρ g x ∈ (R.FW i).MK) := by
      intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      subst hfx
      obtain ⟨h1, h2⟩ := h0 g f
      rw [← h2]
      refine ⟨(t.e i _).2, fun hm => (t.mem_MK i _).2 ?_⟩
      exact GlobalTheory.LevActInt.intAll_actLev T κ i (O i).lev2 t.laws hact g f ⟨_, h1⟩ rfl ((t.mem_MK i f).1 hm)
    exact ⟨fun hx => (key hx).1, fun hx => (key hx.1).2 hx⟩
  · intro g x
    rw [(hr i).2 hk g]
    exact ⟨id, id⟩

end



theorem inGeo_and_lUnif_and_lIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  intro hP D G _ _ Pl0 T0 A T _ R ph B hC hχ hp hn
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hJ := GlobalTheory.CuspValues.jEvExists_and_jEvBar D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hI := GlobalTheory.MemberEvalInj.evInj_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hU := GlobalTheory.ReadingSpan.jUnif hP D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp hJ.1 hJ.2 hI hn
  have hL := GlobalTheory.MemberLatFull.latFull_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hG := GlobalTheory.geoAct_of_ties_of_equivAll T R B.κ B.v₀ B.O hC.lev hC.models.inf hC.models.HW ht hp B.pins B.equivAll
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hp B.pins
  refine ⟨⟨hJ.1, hJ.2, hI, hU, hG, hL, B.fw.dimMatch⟩, fun i σ => ?_, fun i => ?_⟩
  · exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).1,
      (GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).2,
      GlobalTheory.TiedUnif.rhoIs_of_eqAt B.fw hC.models.HW hC.models.gW hχ B.bar B.rhoGeo hU i σ
        (fun h hV => B.equivAll i _ h hV (hx i _ h hV))
        fun h hV => B.equivAll i _ (good_resC T h) hV (hx i _ (good_resC T h) hV)⟩
  · exact ⟨B.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie B.fw hL i, mkStable_of_rhoGeo B.fw B.pins B.rhoGeo i⟩

end GlobalTheory.RealGeoIn
end
end
