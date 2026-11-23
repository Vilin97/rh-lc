module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPhiHatIndPhi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCoefficientEmbeddingNormLeOfL1Bound
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

theorem petW_le_of_homN_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ) (f : Rul Y.d.Xo₂ Y.d.c₂) (B : ℝ), 0 ≤ B → (∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r, z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom → AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) → AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ f ≤ B ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ f ≤ B := by
  intro D T j Y G σ f B hB h
  have key : ∀ μ : MeasureTheory.Measure (AutQ (D.sp.W j)), μ Set.univ ≤ 1 →
      AllWt.petAt (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) μ G f ≤ B := by
    intro μ hμ
    rw [AllWt.petAt_eq]
    have hb : ∀ q : AutQ (D.sp.W j), ‖AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
        (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)‖ₑ ≤ ENNReal.ofReal B := by
      intro q
      rw [Real.enorm_eq_ofReal (AllWt.homN_nonneg _ _ _ _ _)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).2 ∈
          ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).1).dom
      · exact h _ hz
      · have h0 : AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
            (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out) = 0 := by
          simp [AllWt.homN, AllWt.ptN, rdU, hz, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
        rw [h0]; exact hB
    have h1 : MeasureTheory.eLpNorm' (fun q : AutQ (D.sp.W j) =>
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
          (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)) 2 μ ≤
        MeasureTheory.eLpNorm' (fun _ : AutQ (D.sp.W j) => B) 2 μ := by
      apply MeasureTheory.eLpNorm'_mono_eNorm_ae (by norm_num)
      exact Filter.Eventually.of_forall (fun q => by simpa [Real.eNorm_eq_ofReal hB] using hb q)
    rw [MeasureTheory.eLpNorm'_const B (by norm_num), Real.eNorm_eq_ofReal hB] at h1
    have h2 : MeasureTheory.eLpNorm' (fun q : AutQ (D.sp.W j) =>
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
          (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)) 2 μ ≤ ENNReal.ofReal B := by
      exact h1.trans ((mul_le_mul_right (ENNReal.rpow_le_one hμ (by positivity)) _).trans (by simp))
    exact ENNReal.toReal_le_of_le_ofReal hB h2
  refine ⟨key _ ?_, fun Z => key _ (AllWt.muPart_univ_le _ _ _)⟩
  rw [← AllWt.muPart_univ (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ))]
  exact AllWt.muPart_univ_le _ _ _




theorem nrm_le_of_eq_smul (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ)
    (w : Y.V G) (f : Rul Y.d.Xo₂ Y.d.c₂) (Na : ℕ) (A B : ℝ) (hB : 0 ≤ B) (hA : (Na : ℝ) ≤ A)
    (hc : (w : Rul Y.d.Xo₂ Y.d.c₂) = (Na : Y.d.c₂.F) • f)
    (h : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r,
      z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom →
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) :
    Y.nrm G σ w ≤ A * B ∧
      ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ A * B := by
  obtain ⟨h1, h2⟩ := petW_le_of_homN_le D T j Y G σ f B hB h
  have hn1 : ‖σ (Na : Y.d.c₂.F)‖ = Na := by rw [map_natCast, Complex.norm_natCast]
  have hN0 : (0 : ℝ) ≤ Na := Nat.cast_nonneg _
  refine ⟨?_, fun Z => ?_⟩
  · show AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ _
    rw [hc, AllWt.petW_smul, hn1]
    exact (mul_le_mul_of_nonneg_left h1 hN0).trans (mul_le_mul_of_nonneg_right hA hB)
  · rw [hc, AllWt.petOn_smul, hn1]
    exact (mul_le_mul_of_nonneg_left (h2 Z) hN0).trans (mul_le_mul_of_nonneg_right hA hB)

theorem span_eq_top_of_multiples {F M : Type*} [Field F] [CharZero F] [AddCommGroup M] [Module F M] (W : Submodule F M)
    (S S' : Set W) (hS : Submodule.span F S = ⊤) (Na : ℕ) (hNa : 0 < Na)
    (h : ∀ y ∈ S, ∃ s : F, s ≠ 0 ∧ ∀ y₁ : W, (y₁ : M) = s • (y : M) →
      ((Na • y₁ : W) : M) = (Na : F) • (s • (y : M)) → Na • y₁ ∈ S') :
    Submodule.span F S' = ⊤ := by
  rw [eq_top_iff, ← hS, Submodule.span_le]
  intro y hy
  obtain ⟨s, hs, hm⟩ := h y hy
  have hm' := hm (s • y) rfl (by rw [Nat.cast_smul_eq_nsmul]; rfl)
  have hNa' : ((Na : F)) ≠ 0 := by exact_mod_cast hNa.ne'
  have e1 : y = (s⁻¹ * (Na : F)⁻¹) • (Na • (s • y)) := by
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul, mul_assoc s⁻¹, inv_mul_cancel₀ hNa', mul_one,
      inv_mul_cancel₀ hs, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm')

theorem exp_consts (CA CB CC Q κ : ℝ) :
    Real.exp (CC * Q * κ) * (Real.exp (391 * Q * κ) * Real.exp (CA * Q * κ) * Real.exp (CB * Q * κ)) =
      Real.exp ((CA + CB + CC + 391) * Q * κ) := by
  simp only [← Real.exp_add]
  congr 1
  ring


end GlobalTheory.CovGmin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLattice

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SmallScal



theorem exists_small_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  intro E _ _ _ H Dw l c n La hU
  haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c
  obtain ⟨𝔞, h0, h1, h2⟩ := GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left
    (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by
      obtain ⟨a, ha, h⟩ := GlobalTheory.BetaEx.exists_smul_std m
      exact ⟨a, ha, La.La.smul_mem a hm, h⟩)
  set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx
  have h2' : Ideal.absNorm 𝔞 = idx := h2
  have hidx0 : idx ≠ 0 := by
    rw [← h2']; exact fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)

  have e : ∀ τ, idealAt c La.Ln τ =
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ := by
    intro τ
    unfold idealAt
    rw [← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln),
      ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]
    have := GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)
    rw [← h1] at this
    exact this
  let φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F) := fun τ => RingOfIntegers.mapRingHom (embF c τ)
  let B : FractionalIdeal (𝓞 c.F)⁰ c.F :=
    ∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ

  have hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤
      (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) := by
    intro τ
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤
      (B : Submodule (𝓞 c.F) c.F) := by
    have : (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B := rfl
    rw [this, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_pow]
    exact pow_le_pow_left' (hS τ) _

  obtain ⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F := ⟨_, rfl⟩
  have hnF : Module.finrank ℚ c.F = 2 * k := hk ▸ IsTotallyComplex.finrank c.F
  have hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have hk0 : k ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := c.F); omega
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F :=
    (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1
  have hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k := by
    rw [GlobalTheory.RefSum.sum_mult]
    obtain ⟨t, ht⟩ := hdvd
    have hE0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ht, hnE] at hnF
    have : InfinitePlace.nrComplexPlaces E * t = k := by linarith
    rw [← this]; ring
  have hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k := by
    simp only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]
    simp only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']
    rw [← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]
    push_cast
    ring
  have hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _
  have hB0 : B ≠ 0 := by
    intro hB
    have := hNB
    rw [hB, map_zero] at this
    have h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))
    exact h' this.symm

  set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef
  set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hg : 0 < R / X := div_pos hR0 hX0
  have hcard : Fintype.card (InfinitePlace c.F) = k := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]
  have hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero c.F)
    exact_mod_cast this
  have hdR : |(discr c.F : ℝ)| ≤ R ^ k := by
    rw [hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) < Module.finrank ℚ c.F := by exact_mod_cast Module.finrank_pos
    have hfs := GlobalTheory.CovTop.log_rd_le_fieldSz c.F
    have hlog := Real.log_natCast_nonneg (Module.finrank ℚ c.F)
    have : Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F := by
      rw [div_le_iff₀ hn] at hfs; linarith
    rw [hnF] at this
    push_cast at this ⊢
    linarith
  have hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)| :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)| := Real.sqrt_pos.2 (by linarith)
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0))
    (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by
      rw [Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk,
        div_pow]
      push_cast
      rw [← hXdef]
      have hXk : 0 < X ^ k := pow_pos hX0 k
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']
      calc (2 : ℝ) ^ k * Real.sqrt |(discr c.F : ℝ)| < Real.pi ^ k * Real.sqrt |(discr c.F : ℝ)| :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hk0) hsq0
        _ ≤ Real.pi ^ k * R ^ k := by gcongr; exact hsq.trans hdR)
  refine ⟨b, hb0, ?_, fun σ => ?_⟩
  ·
    have hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1 := by
      have h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) :=
        Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)
      calc Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F)
          ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) * (B : Submodule (𝓞 c.F) c.F) :=
            mul_le_mul' h1' le_rfl
        _ = 1 := by rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hB0, FractionalIdeal.coe_one]
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    rw [← mul_assoc]
    calc Submodule.span (𝓞 c.F) {b} * (∏ τ : E →+* ℂ,
            Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ) *
            ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ
        ≤ 1 * ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ :=
          mul_le_mul' ((mul_le_mul' le_rfl hSB).trans hsb) le_rfl
      _ = _ := one_mul _
  ·
    have h1 := hbw (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h1
    have h3 : ‖σ b‖ ^ 2 < R / X := (Real.lt_sqrt (norm_nonneg _)).1 h1
    rw [lt_div_iff₀ hX0] at h3
    exact h3.le

end GlobalTheory.SmallScal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLatticeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  first | exact @GlobalTheory.SmallScal.exists_small_scalar | exact GlobalTheory.SmallScal.exists_small_scalar | (intros; apply GlobalTheory.SmallScal.exists_small_scalar <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsGoodCoverAtMinimalLevel

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovGmin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem minimal_level_cover_is_good : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  intro _
  obtain ⟨CA, hCA0, hA⟩ := GlobalTheory.CovGmin.span_thFam
  obtain ⟨CB, hCB0, hB⟩ := GlobalTheory.RawThetaSup.homN_smul_raw_le
  obtain ⟨CC, hCC0, hC⟩ := GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral
  refine ⟨CA + CB + CC + 391, by linarith only [hCA0, hCB0, hCC0], ?_⟩
  intro D T hJ j hp hq hf hj Y e o hG Lb hL hM hE hfr ho a n hDom hev hn hpos hsz
  have hH : GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n :=
    ⟨hJ, hp, hq, hf, hj, hG, hL, hM, hE, hfr, ho, hDom, hev, hn, hpos, hsz⟩
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂
  obtain ⟨Na, hNa, hlog, hint⟩ := hC D T j Y e o Lb a n hH nab hnab
  have hspan := hA D T j Y e o Lb a n hH nab hnab
  have hB' := hB D T j Y e o Lb a n hH nab hnab
  clear hA hB hC
  have hκ : 1 ≤ sizeK (T.Q.Dw j) a n := by
    have h1 := GlobalTheory.RawThetaSup.two_mul_card_psi T.Q.H
    have h2 : 1 ≤ n / 2 * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    have h3 : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) := by
      exact_mod_cast h2
    rw [GlobalTheory.RawThetaSup.sizeK_eq]
    exact h3.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hNaE : (Na : ℝ) ≤ Real.exp (CC * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.2 hNa)).1 hlog
  have hFE : Real.exp (fieldSz Y.d.c₂.F) ≤ Real.exp (391 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    Real.exp_le_exp.2 ((hG.size.trans ho).trans
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) (sq_nonneg _)) hκ))
  refine ⟨{w | w ∈ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ ∀ σ, Y.nrm (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)}, fun _ h => h.1, ?_, fun _ h => h.2⟩
  refine span_eq_top_of_multiples (Y.V (wtZ a n)) _ _ hspan Na hNa ?_
  rintro y ⟨x0, La, N, P, -, hU, hTb, hTM, hO, hP, hρ, hy⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n La hU
  refine ⟨s, hs0, fun y₁ hy₁ hc => ⟨hint x0 La N P hU hTb hTM hO hP y hy s hs1 y₁ hy₁, fun σ => ?_⟩⟩
  have hsup := hB' _ x0 La N P hU hTM hO hP hρ y hy s _ (Real.exp_pos _).le
    (fun σ => (hs2 σ).trans (pow_le_pow_left₀ (Real.exp_pos _).le hFE 2)) σ
  have hfin := nrm_le_of_eq_smul D T.toCore j Y (wtZ a n) σ _ _ Na _ _
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le) hNaE hc hsup
  rw [exp_consts] at hfin
  exact hfin
end GlobalTheory.CovGmin
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_good_cover_at_minimal_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  first | exact @_root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | exact _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good | (intros; apply _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good <;> assumption)
end
end
end
