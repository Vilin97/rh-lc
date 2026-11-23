module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PID
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceIntegralRestrict
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SpBlkSurj
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.UCharOf

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockP

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem bp_filter_eq_map {n : ℕ} (ε : Fin n → Bool) (b : Bool) :
    (univ.filter fun i : Fin n => ε i = b) =
      univ.map ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl).toEmbedding := by
  exact (Finset.map_orderEmbOfFin_univ _ rfl).symm

theorem bp_prod_blk {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (b : Bool)
    (g : Fin n → M) :
    ∏ i ∈ univ.filter (fun i : Fin n => ε i = b), g i = ∏ r, g (blk ε b r) := by
  rw [bp_filter_eq_map, Finset.prod_map]
  rfl

theorem bp_split {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → M) :
    ∏ i, F i = (∏ r, F (blk ε true r)) * ∏ r, F (blk ε false r) := by
  rw [← bp_prod_blk ε true F, ← bp_prod_blk ε false F,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => ε i = true)]
  congr 2

theorem bp_blk_surj {n : ℕ} (ε : Fin n → Bool) (b : Bool) (i : Fin n) (h : ε i = b) :
    ∃ r, blk ε b r = i := by
  have hi : i ∈ univ.filter fun i : Fin n => ε i = b := by simp [h]
  rw [bp_filter_eq_map] at hi
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hi
  exact ⟨r, hr⟩

theorem bp_blk_disj {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) (s : Fin (cnt ε false)) :
    blk ε true r ≠ blk ε false s := by
  intro h
  have h1 : ε (blk ε true r) = true := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = true) rfl r
    simpa [blk] using this
  have h2 : ε (blk ε false s) = false := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = false) rfl s
    simpa [blk] using this
  rw [h, h2] at h1
  exact Bool.false_ne_true h1

theorem bp_wden {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) :
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) := by
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  have hsame : ∀ (b : Bool) (r r' : Fin (cnt ε b)),
      (if blk ε b r < blk ε b r' ∧ ε (blk ε b r) = ε (blk ε b r') then t (blk ε b r) - t (blk ε b r') else 1) =
        (if r < r' then (t ∘ blk ε b) r - (t ∘ blk ε b) r' else 1) := by
    intro b r r'
    rw [hmem b r, hmem b r']
    simp only [and_true, Function.comp_apply, (blk_strictMono ε b).lt_iff_lt]
  have hother : ∀ (b b' : Bool), b ≠ b' → ∀ (r : Fin (cnt ε b)) (s : Fin (cnt ε b')),
      (if blk ε b r < blk ε b' s ∧ ε (blk ε b r) = ε (blk ε b' s) then t (blk ε b r) - t (blk ε b' s) else 1) = 1 := by
    intro b b' hbb r s
    rw [if_neg]
    rintro ⟨_, h⟩
    rw [hmem b r, hmem b' s] at h
    exact hbb h
  unfold wdenK wden
  rw [bp_split ε]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother true false (by decide) r s), mul_one]
    exact Finset.prod_congr rfl fun r' _ => hsame true r r'
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother false true (by decide) r s), one_mul]
    exact Finset.prod_congr rfl fun r' _ => hsame false r r'

theorem bp_rho {n : ℕ} (ε : Fin n → Bool) (b : Bool) : rhoK ε ∘ blk ε b = delta (cnt ε b) := by
  have hmem : ∀ s : Fin (cnt ε b), ε (blk ε b s) = b := fun s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  funext r
  simp only [Function.comp_apply, rhoK, delta, hmem r]
  have hset : (univ.filter fun j : Fin n => blk ε b r < j ∧ ε j = b) =
      (Finset.Ioi r).map ⟨blk ε b, (blk_strictMono ε b).injective⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Ioi,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hlt, hj⟩
      obtain ⟨s, hs⟩ := bp_blk_surj ε b j hj
      rw [← hs] at hlt
      exact ⟨s, (blk_strictMono ε b).lt_iff_lt.mp hlt, hs⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(blk_strictMono ε b) hs, hmem s⟩
  rw [hset, Finset.card_map, Fin.card_Ioi]
  have := r.isLt
  omega

theorem bp_alt_eq_sum {K : Type*} [Field K] (n : ℕ) (a : Fin n → ℤ) (t : Fin n → K) :
    alt n a t = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i := by
  unfold alt
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [Matrix.of_apply]

def bp_e {n : ℕ} (ε : Fin n → Bool) : Fin (cnt ε true) ⊕ Fin (cnt ε false) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (blk ε true) (blk ε false)) (by
    constructor
    · rintro (r | r) (s | s) h
      · exact congrArg Sum.inl ((blk_strictMono ε true).injective h)
      · exact absurd h (bp_blk_disj ε r s)
      · exact absurd h.symm (bp_blk_disj ε s r)
      · exact congrArg Sum.inr ((blk_strictMono ε false).injective h)
    · intro i
      cases hb : ε i
      · obtain ⟨r, hr⟩ := bp_blk_surj ε false i hb
        exact ⟨Sum.inr r, hr⟩
      · obtain ⟨r, hr⟩ := bp_blk_surj ε true i hb
        exact ⟨Sum.inl r, hr⟩)

theorem bp_e_inl {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) :
    bp_e ε (Sum.inl r) = blk ε true r := rfl

theorem bp_e_inr {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε false)) :
    bp_e ε (Sum.inr r) = blk ε false r := rfl

theorem bp_phi_inl {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε true)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε true r) = blk ε true (α r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inl ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inl, bp_e_inl]

theorem bp_phi_inr {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε false)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε false r) = blk ε false (β r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inr ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inr, bp_e_inr]

theorem bp_num {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) :
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) := by
  classical
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  rw [bp_alt_eq_sum, bp_alt_eq_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  unfold numK
  symm
  refine Finset.sum_bij (fun p _ => (bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    obtain ⟨x, rfl⟩ := (bp_e ε).surjective i
    rcases x with r | r
    · rw [bp_e_inl, bp_phi_inl, hmem, hmem]
    · rw [bp_e_inr, bp_phi_inr, hmem, hmem]
  · intro p _ q _ h
    exact Equiv.Perm.sumCongrHom_injective ((Equiv.permCongr (bp_e ε)).injective h)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hmaps : Set.MapsTo ((bp_e ε).symm.permCongr σ) (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr'⟩ := bp_blk_surj ε true (σ (blk ε true r)) (by rw [hσ, hmem])
      refine ⟨r', ?_⟩
      rw [Equiv.permCongr_apply, Equiv.symm_symm, bp_e_inl, ← hr', ← bp_e_inl, Equiv.symm_apply_apply]
    obtain ⟨q, hq⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    refine ⟨q, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    have hq' : Equiv.Perm.sumCongr q.1 q.2 = (bp_e ε).symm.permCongr σ := hq
    rw [hq']
    ext i
    simp [Equiv.permCongr_apply]
  · intro p _
    rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      bp_split ε (fun i => t (((bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) i) ^ a i)]
    simp only [bp_phi_inl, bp_phi_inr, Function.comp_apply, Units.val_mul, Int.cast_mul]
    ring

theorem blockComb : BlockCombStatement := by
  intro K _ n ε a t
  exact ⟨bp_wden ε t, bp_num ε a t, bp_rho ε⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Weyl

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem weyl : WeylStatement :=
  weyl_of (kCharGT_of (uChar_of sqChar)) blockComb

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqOfMem

section

@[expose] public section

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev dMode blockAlg topP detbP OmP)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem trace_eq_of_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H)
    (L : Submodule ℂ H) [FiniteDimensional ℂ L] (hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L) {c : ℂ} (hc : HasTrace B c) :
    c = LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) := by
  have hle : LinearMap.range (B : H →ₗ[ℂ] H) ≤ L := by rintro _ ⟨x, rfl⟩; exact hB x
  have := Submodule.finiteDimensional_of_le hle
  rw [← hc.2, (hasTrace_of_finiteRank B).2, finRankTrace_eq _ L hB]

theorem equiv_of_index (hR : RangeFD) (hY : BuildY) (hS : StrKer) (hI : StrIdx) (hA : AvgMap) (hH : HWVec)
    (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv) (hCS : CompanionTheory.D.gk.HC.CasScal)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hstd : StdGap ε lam) (h3 : Gap3 ε lam)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {T : Mat n → (W →L[ℂ] W)}
    (hT : IsKIrr ε (gaW ε lam) T) {P : Poly n} (hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (B : H →L[ℂ] H)
    (hB : ∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) {c : ℂ}
    (hc : HasTrace B c) (hc0 : c ≠ 0)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x) := by
  have hDer := isDerivedOn_smE hσ
  obtain ⟨d, hd⟩ := hI n ε P
  obtain ⟨L, hLf, hLK, hLr⟩ := hR n ε H σ hσ hirr d
  obtain ⟨cas, hcas⟩ := hCS n ε H σ hσ hirr
  obtain ⟨Y, hYf, hle, hYP, hYD, hG, hK⟩ := hY n ε H σ _ _ hσ hDer cas hcas L hLf hLK
  obtain ⟨hBL, htr⟩ := hd H σ _ _ hσ hDer L hLK hLr Y hle hYP hG hK B hB
  obtain ⟨Z, hZf, hZK, Γ, hZY, hZD, hZtr⟩ := hS n ε H σ _ _ hσ hDer Y hYD hG hK
  have hLH : FiniteDimensional ℂ (L.map (smD ε σ).subtype) := Module.Finite.map _ _
  have h1 := (trace_eq_of_mem B _ hBL hc).trans htr
  obtain ⟨Φ, hΦ0, hΦ⟩ := hA n ε W T (TSub Z) (tOp hDer hZK) Γ hT.2.1 (tOp_isURepOn hDer hZK hσ) (by
    intro h0
    apply hc0
    rw [h1, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hZtr (toMK k) k.2, hP (toMK k) k.2])
  obtain ⟨z, hzZ, hz0, hz⟩ := hH n ε H σ _ _ hσ hDer Z hZK _ W T hT Φ hΦ0 hΦ
  obtain ⟨hSf, hSk⟩ := hC n ε _ (smE ε σ) Z hZf fun a b hab y hy => diagE_mem_of_wK hσ hDer Z hZf hZK hab hy
  obtain ⟨V, hV, hV0, hVc⟩ := hAlg n ε lam h3 _ (smE ε σ) hDer.glRep (isInfUnitary_of_isDerivedOn hσ hDer) z hz0
    (hYP (hZY hzZ)) hz (hCas n ε lam _ _ hDer.glRep z hz (hZD z hzZ)) _ hSf hSk
    fun s => Submodule.subset_span ⟨s, z, hzZ, rfl⟩
  exact hE n ε lam hstd H σ hσ hirr V hV hV0 hVc X D hD

theorem exists_type (hCp : CptCase) (hSch : SchurOne)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hHC : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hthr : thrStar ε < h) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε (gaW ε lam) T ∧ ∀ P : Poly n,
      (∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P) → ∀ (B : X →L[ℂ] X) (c : ℂ),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • D (toMK k) w ∂(muK ε)) → HasTrace B c →
      c = (-1) ^ sDeg ε := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨hpd, hs, hX⟩ := hCp n ε lam hpq
    obtain ⟨hfd, hT⟩ := hX X D hD
    refine ⟨X, inferInstance, inferInstance, hfd, D, hT, fun P hP B c hB hc => ?_⟩
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
      simp only [hpd, mul_one]
      refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun p => ?_)
      rcases p with p | p
      · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous)
      · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous))
    have h1 := trace_integral_restrict (μ := muK ε) (⊤ : Submodule ℂ X) hcont (fun k => D (toMK k))
      (fun v => (hT.2.1.2.2 v).comp_continuous hemb.continuous fun k => k.2) (fun _ _ _ => trivial) B hB
      (fun _ _ => trivial)
    rw [trace_eq_of_mem B ⊤ (fun _ => trivial) hc, h1, hs, pow_zero, ← hSch n ε _ X D hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hpd, mul_one, hP (toMK k) k.2]
    delta trK
    congr 1
    exact LinearMap.trace_restrict_eq_of_forall_mem ⊤ _ fun _ => trivial
  · obtain ⟨W, i1, i2, i3, T, h1, h2, h3, h4⟩ := supTrace n ε lam h X D hD hHC hh hthr (by omega) (by omega)
    refine ⟨W, i1, i2, i3, T, ⟨h1, h2, h3⟩, fun P hP B c hB hc => ?_⟩
    obtain ⟨hf, htr⟩ := h4 P B hB
    rw [trace_eq_of_mem B _ (fun x => LinearMap.mem_range_self _ x) hc, htr]
    have h5 := hSch n ε _ W T ⟨h1, h2, h3⟩
    rw [← mul_one ((-1 : ℂ) ^ sDeg ε), mul_assoc, one_mul, ← h5]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hP (toMK k) k.2]
    rfl

theorem stKData_of (hBF : BlockForm) (hOm : OmDet) (hCP : CoefPoly) (hTP : TrPoly) (hCl : ClassFn) (hGa : GaInt)
    (hTK : ToKType) (hPT : PhysTor) (hTor : TorusId) (hA : AvgMap) (hSch : SchurOne) (hR : RangeFD) (hY : BuildY)
    (hS : StrKer) (hI : StrIdx) (hH : HWVec) (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv)
    (hCp : CptCase) (hGap : GapNum) (hM : MatRep) (hCS : CompanionTheory.D.gk.HC.CasScal) : GlobalTheory.PsCo.Pc1.StKData := by
  intro r hr ε lam hg X _ _ D hD
  have := hD.1
  obtain ⟨hHC, hstd, h3, h, hh, hthr⟩ := hGap r hr ε lam hg
  obtain ⟨W, _, _, _, T, hT, hidx⟩ := exists_type hCp hSch hHC hh hthr hD
  have hcoef := hCP r ε W T hT.2.1
  obtain ⟨P, hP⟩ := hTP r ε W T hcoef
  replace hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P := hP
  obtain ⟨Q, hQ⟩ := hOm r ε
  obtain ⟨M, R, hRb, hRe⟩ := hBF r ε (MvPolynomial.C ((-1 : ℂ) ^ sDeg ε) * P * Q)
  have hsq : ((-1 : ℂ) ^ sDeg ε) * (-1) ^ sDeg ε = 1 := by rw [← mul_pow]; simp
  have htop : ∀ k ∈ Formalism.REAL.Kset ε, ev k (topP ε M R) = (-1) ^ sDeg ε * (ev k P * physDet ε k) := by
    intro k hk
    change ev k (detbP r ^ M * R * (OmP ε).det) = _
    rw [map_mul, ← hRe k hk, ← hQ k hk, map_mul, map_mul,
      show ev k (MvPolynomial.C _) = _ from MvPolynomial.eval_C _]
    ring
  have hscale : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (A : KG ε → (H →L[ℂ] H)) (B : H →L[ℂ] H) (c : ℂ),
      (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M R) • A k v ∂(muK ε)) → HasTrace B c →
      (∀ v, (((-1 : ℂ) ^ sDeg ε) • B) v = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • A k v ∂(muK ε)) ∧
        HasTrace (((-1 : ℂ) ^ sDeg ε) • B) ((-1) ^ sDeg ε * c) := by
    intro H _ _ _ A B c hB hc
    refine ⟨fun v => ?_, ⟨hc.1.smul _, by rw [trace_smul, hc.2]⟩⟩
    rw [_root_.smul_apply, hB, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [htop (toMK k) k.2, smul_smul, ← mul_assoc, hsq, one_mul]
  refine ⟨M, R, hRb, fun k k' => ?_, fun θ hθ => ?_, fun B c hB hc => ?_, fun U _ _ _ π hπ hi hne B c hB hc => ?_⟩
  · rw [htop _ (k'⁻¹ * k * k').2, htop _ k.2, ← hP _ (k'⁻¹ * k * k').2, ← hP _ k.2, (hCl r ε k k').1,
      (hCl r ε k k').2 W T hT.2.1]
  · obtain ⟨Λ, m, hΛ, hdom, hm, hsh⟩ := hGa r ε _ hHC
    have hk : Matrix.diagonal (tor θ) ∈ Kset ε := diag_mem_Kset' ε θ
    rw [hΛ] at hT
    obtain ⟨T₀, hT₀⟩ := hTK r ε _ W T hT hcoef
    have hw := ReciprocityTheory.ChartRestriction.TR.Weyl.weyl r ε Λ hdom T₀ (HW.torepK ε hk) (tor θ) rfl
    rw [hT₀] at hw
    have h1 := hTor r ε _ Λ m hm hsh θ hθ _ hw
    change (-1) ^ sDeg ε * trK T (Matrix.diagonal (tor θ)) = _ at h1
    change ev (Matrix.diagonal (tor θ)) _ = _
    have h2 := congrArg conj h1
    rw [map_mul, map_mul, map_pow, map_neg, map_one] at h2
    rw [htop _ hk, ← hP _ hk, ← (hPT r ε θ).2, ← mul_assoc, h2]
    ring
  · obtain ⟨h1, h2⟩ := hscale X (fun k => D (toMK k)) B c hB hc
    have h4 := hidx P hP _ _ h1 h2
    have h5 := congrArg (fun x => (-1 : ℂ) ^ sDeg ε * x) h4
    simpa only [← mul_assoc, hsq, one_mul] using h5
  · by_contra hc0
    obtain ⟨σ, hσ, hirr, hσπ⟩ := hM r ε U π hπ hi
    obtain ⟨h1, h2⟩ := hscale U (fun k => π k) B c hB hc
    obtain ⟨A, hAe⟩ := equiv_of_index hR hY hS hI hA hH hC hCas hAlg hE hCS hstd h3 hT hP hσ hirr _
      (fun w => by rw [h1 w]; simp only [toMK, hσπ]) h2
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc0) hD
    exact hne ⟨A, fun g v => by rw [← hσπ g]; exact hAe _ g.2 v⟩

end GlobalTheory.PsCo.PcEF
end
end
end
