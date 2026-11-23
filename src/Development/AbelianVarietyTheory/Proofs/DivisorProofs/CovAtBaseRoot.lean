module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatOfInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFifth
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Mathlib.Algebra.Azumaya.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightZeroConstFrameValueMemCoeffRange

section

@[expose] public section

noncomputable section

namespace GlobalTheory.FlatLine


open IntermediateField in
theorem mem_range_of_embeddings_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Countable Ω] [Algebra K Ω]
    [Algebra K ℂ] (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {a : ℂ} (h : ∀ P : Ω →ₐ[K] ℂ, P b = a) :
    a ∈ (algebraMap K ℂ).range := by
  have hb : IsIntegral K b :=
    (isAlgebraic_of_norm_const P₀ fun P => by rw [h P, h P₀]).isIntegral
  haveI : FiniteDimensional K K⟮b⟯ := adjoin.finiteDimensional hb
  have key : ∀ ψ : K⟮b⟯ →ₐ[K] ℂ, ψ (AdjoinSimple.gen K b) = a := fun ψ => by
    letI : Algebra K⟮b⟯ ℂ := ψ.toRingHom.toAlgebra
    obtain ⟨Q⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K⟮b⟯ Ω
    let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
      commutes' := fun k => (Q.commutes (algebraMap K K⟮b⟯ k)).trans (ψ.commutes k) }
    rw [← h P]
    exact (Q.commutes (AdjoinSimple.gen K b)).symm
  have hsub : Subsingleton (K⟮b⟯ →ₐ[K] ℂ) := ⟨fun ψ χ =>
    (adjoin.powerBasis hb).algHom_ext (by rw [adjoin.powerBasis_gen, key, key])⟩
  have h1 : Module.finrank K K⟮b⟯ = 1 := by
    have h2 := AlgHom.card K K⟮b⟯ ℂ
    have h3 : Fintype.card (K⟮b⟯ →ₐ[K] ℂ) ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have h4 : 0 < Module.finrank K K⟮b⟯ := Module.finrank_pos
    omega
  obtain ⟨k, hk⟩ := mem_bot.1 (finrank_adjoin_simple_eq_one_iff.1 h1)
  exact ⟨k, by rw [← h P₀, ← hk, P₀.commutes]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt

theorem const_value_mem_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q →
    ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 g hg a ha
  obtain ⟨hL, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c h1).1
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, toC (P (evC h Z g)) = a := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (one_mul _).trans (ha k x x.2)
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  haveI hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
  have hO : Countable (Om Z) := GlobalTheory.GenericReading.countable_fractionRing_mvPolynomial _ _
  letI : Algebra c.F ℂ := σ.toAlgebra
  exact mem_range_of_embeddings_const (K := c.F) (b := evC h Z g) P₀ key

end GlobalTheory.FlatLine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightZeroConstFrameValueMemCoeffRangeStatement

section

@[expose] public section

open NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  first | exact @GlobalTheory.FlatLine.const_value_mem_range | exact GlobalTheory.FlatLine.const_value_mem_range | (intros; apply GlobalTheory.FlatLine.const_value_mem_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovAtBaseRoot

section

@[expose] public section

namespace GlobalTheory.AdTh.CoverRoot

section Core

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdTh.CoverVal

theorem rdU_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (k : U.Comp) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) {b : Frame (U.X k).Ψ r} (hb : b ∈ Bor (U.X k).Ψ r) :
    rdU U f k (rmul (lact γ x) b) = rdU U f k x := by
  have hs := hU.2.2.2.2.1 0 0 ⟨fun τ _ _ _ => le_rfl, Even.zero⟩ f hf k
  rw [show laU U 0 0 k = 0 from GlobalTheory.Reg.IdemCusp.laU_zero (Formalism.L2.PjFree.Unf.ofPj U) k] at hs
  rw [hs.2.1 _ (dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)) b hb, hs.2.2 γ hγ x hx, GlobalTheory.Reg.IdemCusp.chi_zero _ hγ]
  simp [bchar]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}



theorem covAt_mem (hR : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (c0 : ℂ) (h0 : GlobalTheory.PtId.CovAt O c0) :
    c0 ∈ (inC O.c').range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  obtain ⟨c1, hm, hc⟩ := hO.cxi
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  obtain ⟨hlev, hA, -⟩ := hO.cov ()
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hX₀, hon₀, -, hp₀, hrk, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    hs0 (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ ()).c₂ ((inC O.c').comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  obtain ⟨hroot, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hxi : ∀ x, R.xi A.μ0 x = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0)
  have hf : (O.dδ ()).cδ ∈ sec (O.dδ ()).Xo₂ (O.dδ ()).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c1 := fun h => by
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 h
    obtain ⟨x, hx⟩ := hroot (γ' * h)
    have hv := hval h γ' ⟨hγ', h2, h3⟩
    rw [(hO.tuple ()).xi _ _ hx, hxi, Circle.coe_one, _root_.mul_one] at hv
    exact hv
  have key : ∀ h, (O.dict₂ () h).2 ∈ ((O.U₂ ()).X (O.dict₂ () h).1).dom ∧
      rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨hon, γ, ⟨hγ, hl, hfr⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ ()) hσ hU h1 hA R.θ (Wc D i)
      (rank_Wc i) (O.dict₂ ()) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt h
    obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ _ _ _ (O.dδ ()).c₂ _ _ Wt.g 0 ((O.U₂ ()).X (O.dict₂ () h).1) 0 Wt.e hσ hU.1
      (hU.2.1 _).1 (hU.2.1 _).2 hsd ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon
    have hA' := uw_anFib _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1 Dc.bas Dc.idx
      Dc.sympl hper hty ⟨_, hd'⟩ hu'
    obtain ⟨x, hx⟩ := hroot (γ * h)
    have h3 := h0 () _ Wt.g Dc.bas Dc.idx Wt.e (γ * h) x (Wt.mark (O.dict₂ () h).1) (hmod _) (hU.2.1 _).1 Dc.sympl
      ⟨hper, hty⟩ hl hx hmark hma
    rw [← hfr, hxi, Circle.coe_one, _root_.mul_one] at h3
    obtain ⟨A', hA'', -⟩ := hA'
    exact ⟨hd', (dif_pos hd').trans (h3 _ A' hA'')⟩
  obtain rfl : c0 = c1 := (key 1).2.symm.trans (hv 1)
  refine ⟨?_, hm⟩
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ (inR i) O.s0 (hs0 ▸ T.toCore.good_σ₀) (Wc D i) O.hV
    (rank_Wc i)
  have hpq := hrk ▸ h1
  obtain ⟨a, ha⟩ := GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range _ _ _ _ _ _ _ _ (O.U₂ ()) hσ hU hpq _ hf c0 fun k x hx => by
    obtain ⟨h, γ, hγ, b, hb, e⟩ := GlobalTheory.CoverIndep.dict_onto (Wc D i) (rank_Wc i) (O.U₂ ()) (O.dict₂ ()) (iotaW T i) e' F' ik φ
      th _ hσ hA hpq hU hW hD hio hth hx₀ (fun h => (key h).1) k x hx
    have h4 := hv h
    rw [e] at h4
    exact (rdU_move (O.U₂ ()) hU hf k hx hγ hb).symm.trans h4
  exact ⟨_, ha⟩

end Core

section Top

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem covAt_base_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ c0 : ℂ, GlobalTheory.PtId.CovAt (O i) c0 → c0 ∈ D.what₂.embLL.range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O _ hC i hOP c0 h0
  obtain ⟨⟨a, rfl⟩, hm⟩ := covAt_mem hC ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩ (O i) hOP.2 c0 h0
  refine ⟨?_, hm⟩
  obtain ⟨b, hb⟩ := hOP.1.le a.2
  exact ⟨b, hb⟩

end Top

end GlobalTheory.AdTh.CoverRoot
end
end
