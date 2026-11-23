module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdjointSubstLogarithmsIntoParametersOfLogExponen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
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
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffBivariateSeriesSubstPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffPadicLogSeriesUnramifiedEqZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsFrobWToC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpSNegSumBivariatePairIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusMapSubstPair
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstSumCMul
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffsWpSubst

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

open MvPowerSeries Formalism.MainNotions.GL3Theta

theorem coeffsWp_mul {τ : Type} {p : ℕ} [Fact p.Prime] {f g : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (hg : ∀ m, coeff m g ∈ Wp p) : ∀ m, coeff m (f * g) ∈ Wp p := by
  intro m
  rw [coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem coeffsWp_one {τ : Type} {p : ℕ} [Fact p.Prime] : ∀ m, coeff m (1 : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem coeffsWp_pow {τ : Type} {p : ℕ} [Fact p.Prime] {f : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (k : ℕ) : ∀ m, coeff m (f ^ k) ∈ Wp p := by
  induction k with
  | zero => simpa using coeffsWp_one
  | succ k ih => rw [pow_succ]; exact coeffsWp_mul ih hf

theorem coeffsWp_subst {σ τ : Type} {p : ℕ} [Fact p.Prime] {a : σ → MvPowerSeries τ ℂ_[p]} (ha : HasSubst a)
    (hA : ∀ i m, coeff m (a i) ∈ Wp p) {f : MvPowerSeries σ ℂ_[p]} (hf : ∀ m, coeff m f ∈ Wp p) :
    ∀ m, coeff m (subst a f) ∈ Wp p := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun w => w ∈ Wp p) (Subring.zero_mem _) (fun x y hx hy => Subring.add_mem _ hx hy) ?_
  intro d
  refine Subring.mul_mem _ (hf d) ?_
  have hP : ∀ m, coeff m (d.prod fun s k => a s ^ k) ∈ Wp p := by
    unfold Finsupp.prod
    induction d.support using Finset.induction_on with
    | empty => simpa using coeffsWp_one
    | insert i S hi ih => rw [Finset.prod_insert hi]; exact coeffsWp_mul (coeffsWp_pow (hA i) _) ih
  exact hP e

theorem coeffsWp_X {τ : Type} {p : ℕ} [Fact p.Prime] (t : τ) : ∀ m, coeff m (X t : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hasSubst_copy {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) := by
  have hinj : Function.Injective (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := by
    intro s t h
    simpa using h
  haveI : Filter.TendstoCofinite (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := ⟨hinj.tendsto_cofinite⟩
  exact HasSubst.X_comp (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1))

theorem xiE_props {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p])
    (hx : ∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) :
    constantCoeff (xiE x i) = 0 ∧ ∀ m, coeff m (xiE x i) ∈ Wp p := by
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩

theorem xiE_integral : ∀ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (xiE x i) = 0) ∧ ∀ F : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p), IntS p F → ∀ m, ‖MvPowerSeries.coeff m (MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F))‖ ≤ 1 := by
  intro p _ n' r0 r1 x hx
  have hP := xiE_props (r0 := r0) (r1 := r1) x hx
  refine ⟨fun i => (hP i).1, ?_⟩
  intro F hF m
  obtain ⟨g, rfl⟩ := hF
  have hs : HasSubst (xiE x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → _) :=
    hasSubst_of_constantCoeff_zero fun i => (hP i).1
  have hG : ∀ d, coeff d (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (MvPowerSeries.map (algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p)) g)) ∈ Wp p := by
    intro d
    rw [coeff_map, coeff_map]
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.wToC_mem_Wp p _
  exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (coeffsWp_subst hs (fun i => (hP i).2) hG m)

end GlobalTheory.OnePlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstInLettersJetLogG

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section
namespace GlobalTheory.OnePlace.Letters

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (n' : ℕ) {β : Type} (v : ZMod n' × β) :
    MvPowerSeries.constantCoeff (jetLogG p n' v) = 0 := by
  show jetLogG p n' v 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  have h2 := congrArg (fun m : ZMod n' × β →₀ ℕ => m (v.1 - 2 * (e : ZMod n'), v.2)) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h2
  exact (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)) h2.symm

def posEquiv (n r0 r1 : ℕ) [NeZero n] : Zidx n r0 r1 ≃ ZMod n × Fin r0 × Fin r1 where
  toFun z := (((z.1 : ℕ) : ZMod n), z.2)
  invFun v := (toFin v.1, v.2)
  left_inv z := by
    ext <;> simp [toFin, ZMod.val_natCast, Nat.mod_eq_of_lt z.1.2]
  right_inv v := by
    ext <;> simp [toFin, ZMod.natCast_zmod_val]

theorem coeff_inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R)
    (m : ZMod n × Fin r0 × Fin r1 →₀ ℕ) :
    MvPowerSeries.coeff m (inLetters f) = MvPowerSeries.coeff (Finsupp.mapDomain (posEquiv n r0 r1).symm m) f := rfl

theorem inLetters_eq_rename {n r0 r1 : ℕ} [NeZero n] {R : Type} [CommRing R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    inLetters f = MvPowerSeries.rename (posEquiv n r0 r1) f := by
  ext m
  have hm : m = Finsupp.mapDomain (posEquiv n r0 r1) (Finsupp.mapDomain (posEquiv n r0 r1).symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have h1 := MvPowerSeries.coeff_embDomain_rename (posEquiv n r0 r1).toEmbedding f
    (Finsupp.mapDomain (posEquiv n r0 r1).symm m)
  rw [Finsupp.embDomain_eq_mapDomain] at h1
  rw [coeff_inLetters]
  conv_rhs => rw [hm]
  exact h1.symm

theorem map_inLetters {n r0 r1 : ℕ} [NeZero n] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries.map φ (inLetters f) = inLetters (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, coeff_inLetters, coeff_inLetters, MvPowerSeries.coeff_map]

theorem subst_inLetters_jetLogG {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} [NeZero n'] (F : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) :
    (∀ z, MvPowerSeries.constantCoeff (jetZ p n' r0 r1 z) = 0) ∧
    MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v)
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters F)) =
    MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F) := by
  refine ⟨fun z => constantCoeff_jetLogG p n' _, ?_⟩
  have ha : MvPowerSeries.HasSubst
      (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by
      rw [map_mul, constantCoeff_jetLogG, mul_zero]
  rw [map_inLetters, inLetters_eq_rename, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext z
  rw [Function.comp_apply, MvPowerSeries.subst_X ha, map_one, one_mul]
  rfl

end GlobalTheory.OnePlace.Letters
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WToCPowComm

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wToC_pow_comm {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p])
    (hσ : ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) :
    ∀ (k : ℕ) (x : FormalGroupSystem.WW p), (σ ^ k) (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, hσ, Function.iterate_succ_apply']

theorem dualOm_wToC : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) → ∀ (n' : ℕ), Even n' → ∀ B : OmBasis p n', GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) := by
  intro p _ σ hσ n' hn B
  have hk := wToC_pow_comm σ hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    exact Nat.two_mul_div_two_of_even hn
  · intro r
    exact ⟨Formalism.L2.G.Pend.wToC_mem_Wp p _, Formalism.L2.G.Pend.wToC_mem_Wp p _⟩
  · intro r
    refine ⟨?_, ?_⟩
    · rw [hk, B.fix r]
    · rw [hk, B.fixS r]
  · intro r r'
    have h := congrArg (Formalism.L2.G.Pend.wToC p) (B.dual r r')

    rw [map_sum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i => (σ ^ (2 * i)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r')))]
    simp only [← map_mul, hk]
    rw [h]
    split_ifs <;> simp

end GlobalTheory.TwU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

theorem exists_letterCoordinates_series_onePlace : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ h5 n' _ hev B be hbe
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.TwU.exists_isFrob_wToC p
  have hb0 := GlobalTheory.BeRead.isBe0_map p σ hσ hσw be hbe
  have hb00 : MvPowerSeries.constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) = 0 := by
    by_contra h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact (hb0.axes 0 h).1 rfl
  have hD := GlobalTheory.TwU.dualOm_wToC p σ hσw n' hev B
  obtain ⟨bv, t, x, ⟨h1, h2, h3, h4⟩, hcc, hsim, ht, hx, htla, hxt⟩ :=
    Unr.exists_coords_and_series h5 hσ hb0 n' hev _ _ hD
  refine ⟨bv, h1, h2, h3, h4, fun r0 r1 U hU => ?_⟩
  obtain ⟨V, hV, hVeq⟩ := GlobalTheory.OrbitPair.expS_neg_sum_bivariate_pair_integral σ _ _ _ bv t x hb00 hcc ht hx htla hxt hsim
  obtain ⟨U2, hU2, hU2eq⟩ := GlobalTheory.OnePlacePairs.pairs_all _ bv x V hb00 hcc (fun r => (hx r).2) hV hVeq r0 r1
  obtain ⟨hξ0, hξint⟩ := GlobalTheory.OnePlace.xiE_integral (r0 := r0) (r1 := r1) x hx
  obtain ⟨hJ0, hJ⟩ := GlobalTheory.OnePlace.Letters.subst_inLetters_jetLogG (p := p) (r0 := r0) (r1 := r1) (thOne B be U)
  refine ⟨U2 * MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)), ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_mul]
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_)
    rw [norm_mul]
    exact mul_le_one₀ (hU2 _) (norm_nonneg _) (hξint _ hU _)
  · rw [hJ, GlobalTheory.OnePlaceRead.read_thOne B be hbe U _ (xiE x) hJ0 hξ0 (GlobalTheory.OnePlace.Ident.coordZ_jetZ σ hσw hev B hD t x ht (fun r => (hx r).2) htla hxt r0 r1), hU2eq]
    ring

end GlobalTheory.OnePlace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  first | exact @GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | exact GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | (intros; apply GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace <;> assumption)
end
end
