module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeUnitriangularUnipotentModPlaceStatement
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdealStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelDvdBadN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunModelArch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Formalism.LocalRingCardinality.DataParams
import Mathlib.Algebra.Order.Star.Real
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqPlGwOrIsConjPl

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TypePlacesExhaust

variable {R : Ranks} (H : Host R)

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap ((cInt H).symm : 𝓞 H.E →+* 𝓞 H.E) (cInt H).symm.surjective w

variable {H}

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (y : 𝓞 H.E) :
    y ∈ (conjPl H w).asIdeal ↔ (cInt H).symm y ∈ w.asIdeal := Iff.rfl

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hy
  have e : y = cInt H x := RingOfIntegers.ext (by rw [hy]; rfl)
  subst e
  rw [mem_conjPl, RingEquiv.symm_apply_apply]

theorem conjPl_injective : Function.Injective (conjPl H) := by
  intro w w' h
  apply HeightOneSpectrum.ext
  ext x
  have := congrArg (fun u : HeightOneSpectrum (𝓞 H.E) => cInt H x ∈ u.asIdeal) h
  simp only [mem_conjPl, RingEquiv.symm_apply_apply] at this
  exact Iff.of_eq this

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show ((p : ℕ) : 𝓞 H.E) ∈ (conjPl H w).asIdeal
  rw [mem_conjPl, map_natCast]
  exact hw

theorem finrank_E (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem eq_plGw_or_isConjPl : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  apply GlobalTheory.TypePlaceCover.place_cover <;> assumption

end GlobalTheory.TypePlacesExhaust
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConj

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConjStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  first | exact @GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | exact GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | (intros; apply GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsCompletelyTypePrime

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitsCompletely_typePrime (D : D7) (k : Fin 2) : SplitsCompletely D.host.E (D.host.g k) := by
  refine ⟨D.host.g_prime k, ?_⟩
  have hg0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have h := D.nd.g_split k
  rw [← h]
  have : {P : Ideal (𝓞 D.host.E) | P.IsPrime ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P} =
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) '' {v : HeightOneSpectrum (𝓞 D.host.E) | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} := by
    ext P
    constructor
    · rintro ⟨hP, hg⟩
      have hne : P ≠ ⊥ := fun h0 => hg0 (by rw [h0] at hg; simpa using hg)
      exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, hv⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem half_le_plGw (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (k : Fin 2) (v : D.nd.PlG k) :
    p.T.Q.l.Mb ≤ (D.naut.plGw k v).asIdeal := by
  rw [h.half]
  obtain ⟨plg, -, hplg, -, -, -⟩ := p.grpRecPin
  have hmem : D.naut.plGw k v ∈ (R2 p).Pg := by
    rw [← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  exact (Ideal.prod_le_inf).trans (Finset.inf_le hmem)

theorem levelCondition_restrict_of_halfUnipotent (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) (hg : ∀ k : Fin 2, 3 * D.R.r < D.host.g k)
    (hM : RunModel p r h i M ka) : ∀ H : Subgroup p.P.Gp, HalfUnip p H → LevelHyp (sub M H) := by
  intro H hH
  obtain ⟨k, hk⟩ := hH
  obtain ⟨v0, e, -, -, -, hd1, φ, hd2⟩ := hM
  refine ⟨D.host.g k, splitsCompletely_typePrime D k, hg k, ?_⟩
  intro c β hβ P hP hgP
  obtain ⟨u, huc, γ, hγ, rfl⟩ := hβ
  have huc' : (u : p.P.Gp) • c = c := huc
  have hγL : ∀ w, w ∈ (M.comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' :=
    M.Γ_L' c γ hγ
  have htL : ∀ w, w ∈ (M.comp c).L' ↔
      Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' := by
    intro w
    have := M.tr_L' u c w
    rwa [huc'] at this
  have half : ∀ v : D.nd.PlG k, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec ((((γ * M.tr u c : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) - 1) ^ D.R.r) w ∈
        (D.naut.plGw k v).asIdeal • (M.comp c).L' := by
    intro v w hw
    obtain ⟨n, hn⟩ := hd2 c u huc'
    rw [Units.val_mul]
    exact GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half _ _ _ (half_le_plGw p r h k v) (φ c) (r.lev i u) n (GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace p r h i u k v (hk u u.2 v)) _ _ (fun w hw => (hγL w).1 hw)
      (hd1 c γ hγ) hn w hw
  obtain ⟨v, rfl | rfl⟩ := GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj D k P hP hgP
  · exact half v
  · refine GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal (M.comp c) (γ * M.tr u c) ?_ ?_ _ (half v)
    · intro a b
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((M.comp c).Γ_stab γ hγ).1, M.comp_Gm c, M.tr_herm]
    · intro a
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (htL a).trans (hγL _)

end GlobalTheory.ShareOn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThreeRLtGOfParams

section

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.BigOn

theorem three_r_lt_g_of_params (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (k : Fin 2) :
    3 * D.R.r < D.host.g k := by
  obtain ⟨Y, hY1, -, -, hY4⟩ := P.g_Y
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b
    have := Real.add_one_le_exp L.sc.L
    linarith
  have hmk := D.R.m_add_three_le_k
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hkb : (2 : ℝ) * D.R.k ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hpow : (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 = ((D.R.k : ℝ) * L.sc.b) ^ 8 := by ring
  have h7 : (2 : ℝ) ^ 7 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) 7
  have hbig : (6 : ℝ) * D.R.k < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    rw [← hpow]
    have : (2 : ℝ) * D.R.k * 2 ^ 7 ≤ (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
      mul_le_mul hkb h7 (by norm_num) (by positivity)
    nlinarith
  have hr' : ((3 * D.R.r : ℕ) : ℝ) ≤ 6 * D.R.k := by
    have : 3 * D.R.r ≤ 6 * D.R.k := by omega
    exact_mod_cast this
  have hg : ((3 * D.R.r : ℕ) : ℝ) < (D.host.g k : ℝ) := by
    linarith [(hY4 k).1]
  exact_mod_cast hg

end GlobalTheory.BigOn
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimesGtThreeR

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.BigOn
theorem typePrimes_gt_three_r_alt :
    _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ k : Fin 2, 3 * (Fm.D x i).R.r < (Fm.D x i).host.g k := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i _ _ _ k => three_r_lt_g_of_params _ _ (Fm.params x hx i) k
end GlobalTheory.BigOn
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and _root_.GlobalTheory.ShareOn.p0_extreme_or_archOn_of_runModel _root_.GlobalTheory.BigOn.typePrimes_gt_three_r_alt) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩
end GlobalTheory.ShareOn
end
end
end
end
