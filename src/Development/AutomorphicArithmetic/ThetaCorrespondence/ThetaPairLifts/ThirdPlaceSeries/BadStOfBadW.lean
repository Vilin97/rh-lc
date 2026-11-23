module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamilyStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfRangeAddInfKer

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadOnRec

theorem finrank_inf_range_add_inf_ker {K M : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (e : M →ₗ[K] M) (he : ∀ x, e (e x) = e x) (V : Submodule K M) (hV : ∀ x ∈ V, e x ∈ V) :
    finrank K (V ⊓ LinearMap.range e : Submodule K M) + finrank K (V ⊓ LinearMap.ker e : Submodule K M) = finrank K V := by
  let f : V →ₗ[K] V := e.restrict hV
  have h1 : (LinearMap.range f).map V.subtype = V ⊓ LinearMap.range e := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨hV x x.2, x, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨⟨e z, hy⟩, ⟨⟨e z, hy⟩, Subtype.ext (he z)⟩, rfl⟩
  have h2 : (LinearMap.ker f).map V.subtype = V ⊓ LinearMap.ker e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hk, rfl⟩
  rw [← h1, ← h2, Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  exact LinearMap.finrank_range_add_finrank_ker f

theorem finrank_eq_of_bij {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Bijective f) (p : Submodule K M) (q : Submodule K N) (h : ∀ x, x ∈ p ↔ f x ∈ q) :
    finrank K p = finrank K q := by
  have e : p.map f = q := by
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    constructor
    · rintro ⟨x', hx', e'⟩
      exact hf.1 e' ▸ (h x').1 hx'
    · intro hy
      exact ⟨x, (h x).2 hy, rfl⟩
  rw [← e]
  exact (Submodule.equivMapOfInjective f hf.1 p).finrank_eq

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance runAlgBad {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}

theorem mem_eig_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ F.P0 F.ψ0⁻¹ ph y) (ha : ActionPin h fw ι ℓ)
    (hG : R.IsGrp F) (hinc : F.P0 ≤ inc.range) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ GlobalTheory.OnTies.toForms h fw ι z x ∈ GlobalTheory.CovTop.spType R F ι := by
  have hb := GlobalTheory.OnTies.toForms_bijective h fw ι z
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ ∀ u : O.U, O.ρ i u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ i g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW ι).ρ (inc g) (GlobalTheory.OnTies.toForms h fw ι z x) =
        (((R.FW ι).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • GlobalTheory.OnTies.toForms h fw ι z x :=
    fun g hg => by
      rw [← t.rho_eq_of_actionPin ha, GlobalTheory.OnCoord.chi_eq_one hG ι hg, one_mul, ← t.ψ_eq g hg, ← map_smul, hb.1.eq_iff]
  refine e1.trans ⟨fun hx => ?_, fun hx u => ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := hinc hg
    exact (e2 u hg).1 (hx ⟨u, t.U_eq.ge hg⟩)
  · exact (e2 u (t.U_eq.le u.2)).2 (hx ⟨inc u, t.U_eq.le u.2⟩)

end General

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] runAlgBad

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

end Point

end GlobalTheory.BadOnRec

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadStOfBadW

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.BadOnRec
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}
end General
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] runAlgBad
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem bad_rec_alt (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O) {del : ℝ} (j : Fin D.R.m) (hbad : BadW p j del) :
    (1 - del) * O.d0 j ≤ ((S2 p).D : ℝ) := by
  obtain ⟨hC, hOk, -, -, hRk, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hmem := mem_eig_iff (ht v₁ j).1 (ht v₁ j).2 hC.grp hU
  have hf := finrank_eq_of_bij _ (GlobalTheory.OnTies.toForms_bijective (hrec.1.ok.laws v₁).p (fw2 p) j (z j)) _ _ hmem
  have hd0 : O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) : ℝ) := by
    unfold OnObj.d0
    exact congrArg (fun n : ℕ => (n : ℝ)) hf
  have hV : ∀ x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j, goodOp (R2 p) j x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j :=
    fun x hx g => by
      rw [← GlobalTheory.BigOn.goodOp_rho_comm hOk.irr j (g : p.P.Gp) x, hx g, map_smul]
  have hsplit := finrank_inf_range_add_inf_ker (goodOp (R2 p) j)
    (fun x => LinearMap.congr_fun (goodOp_idem hOk.irr j) x) _ hV
  have hD : (S2 p).D = finrank D.what₂.LL ((R2 p).WL (F2 p) false j) := (hRk.2 j).symm
  have hbad' : (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) :
      Submodule D.what₂.LL _) : ℝ) ≤ del * finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := hbad
  have hs : (finrank D.what₂.LL ((R2 p).WL (F2 p) false j) : ℝ) +
      (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) : Submodule D.what₂.LL _) : ℝ) =
      finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := by
    exact_mod_cast hsplit
  rw [hd0, hD]
  nlinarith
end Point
end GlobalTheory.BadOnRec
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem badSt_of_badW_alt : _root_.GlobalTheory.ShareOn.BadWeightStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement := by
  intro hB
  refine (hB.and GlobalTheory.T.badShareSize_bounds_along_family).imp fun Fm CH _ H => ?_
  obtain ⟨⟨x1, H1⟩, ⟨x2, H2⟩⟩ := H
  refine ⟨0, fun c _ _ => ⟨max x1 x2, fun x hx hle i p hR hm r O hrec => ?_⟩⟩
  have hb := H1 x hx ((le_max_left _ _).trans hle) i p hR hm r hrec.1.ok hrec.2
  have hq := (H2 x hx ((le_max_right _ _).trans hle) i).2.2.1
  intro j
  exact ⟨_, (Real.exp_pos _).le, hq, _root_.GlobalTheory.BadOnRec.bad_rec_alt hR hm hrec j (hb j)⟩
end GlobalTheory.BigOn
end
end
end
end
