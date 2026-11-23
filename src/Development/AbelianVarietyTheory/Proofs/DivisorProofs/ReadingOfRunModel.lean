module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearExtensionOfFormWithTransportedReStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelCuspFormsSpanUsedRunReadingsStatement
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomain

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

theorem _root_.GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom := by
  first | exact @GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | exact GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | (intros; apply GlobalTheory.TwoLevelsDom.lact_tr_mem_dom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingLinearIndependent

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castFrame_castFrame_symm {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (hΨ : Ψ = Ψ')
    (x : Frame Ψ' r) : castFrame hΨ (castFrame hΨ.symm x) = x := by
  subst hΨ; rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem rdLin_linearIndependent {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
    [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ)
    (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) :
    LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  intro hb
  have hJ := (GlobalTheory.ReadingTieCheck.tieRead_holds (h.laws v).p ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩).2 (p.κ i)
  let b' : Fin n → cusp ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c ((r.used v).full.U ((i : ℕ) + 1))
      (wtA (p.κ i)) (p.κ i).n :=
    fun k => ⟨(b k).1, cutR_le (r.used v).full.C ((i : ℕ) + 1) (p.κ i) (b k).2⟩
  have hb' : LinearIndependent (r.used v).full.Q.c.F b' := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h1 ⊢
    exact h1
  have hR := hJ n b' hb'
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro g hg
  apply hR g
  have hoff : ∀ k, rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n (b' k) ∈
      offZero ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X :=
    fun k => rdU_mem_offZero _ _
  have claim : ∀ c, (∑ k, g k • rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n
      (b' k)) (e c) = 0 := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom
    · have hy : castFrame (psi_eq ha c).symm x ∈ M.dom :=
        (mem_dom_iff ha c _).1 (by rw [castFrame_castFrame_symm]; exact hx)
      have := congrFun (congrFun hg c) ⟨_, hy⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rdLin_apply, rdFun,
        castFrame_castFrame_symm] at this
      exact this
    · exact Finset.sum_eq_zero fun k _ => by rw [hoff k (e c) x hx, mul_zero]
  funext k'
  have := claim (e.symm k')
  rw [e.apply_symm_apply] at this
  exact this

end GlobalTheory.ShareOn.Reading
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingLinearIndependentStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cuspForm_family_linearIndependent : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ) (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  first | exact @GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | exact GlobalTheory.ShareOn.Reading.rdLin_linearIndependent | (intros; apply GlobalTheory.ShareOn.Reading.rdLin_linearIndependent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingMemModelCuspForms

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareOn.Reading

theorem cast_mem_SS_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X Y : Data E r} (hXY : X = Y)
    (hΨ : X.Ψ = Y.Ψ) {la : Wt Y.Ψ r} {la' : Wt X.Ψ r}
    (hla : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ Y.Ψ) a, la' ⟨τ, h1⟩ a = la ⟨τ, h2⟩ a) {G : Frame Y.Ψ r → ℂ}
    (hG : G ∈ Y.SS la) : (fun x => G (castFrame hΨ x)) ∈ X.SS la' := by
  subst hXY
  have e : la' = la := by funext τ a; exact hla τ.1 τ.2 τ.2 a
  subst e
  exact hG

theorem rdFun_mem_SS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun (v := v) (e := e) h ha F ∈ M.SS ka := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r h i C _ M ka v e ha hb F c
  have key := GlobalTheory.ReadingTieCheck.reading_mem_SS (h.laws v).p ((i : ℕ) + 1) (p.κ i) F (e c)
  exact cast_mem_SS_of_eq (ha c) ((M.comp_Ψ c).trans (psi_eq ha c)) (fun τ h1 h2 a => hb c τ _ h2 a) key

end GlobalTheory.ShareOn.Reading
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingMemModelCuspFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

theorem _root_.GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  first | exact @GlobalTheory.ShareOn.Reading.rdFun_mem_SS | exact GlobalTheory.ShareOn.Reading.rdFun_mem_SS | (intros; apply GlobalTheory.ShareOn.Reading.rdFun_mem_SS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (GlobalTheory.T.cuspForm_family_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
end
end
end
