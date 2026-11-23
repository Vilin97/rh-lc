module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntryMemSubringOfTraceGramUnitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBddStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitary

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BddCpt

theorem bdd_entries_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  intro E _ _ _ n w t hK
  have hO : IsOpen ((Ov E w : Set (w.adicCompletion E))) := Valued.isOpen_valuationSubring _
  have hNe : (nhdsWithin (0 : w.adicCompletion E) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  have hev : ∀ᶠ a in nhds (0 : w.adicCompletion E),
      ∀ s ∈ closure (Subgroup.zpowers t : Set (UL n w)), ∀ i j, a * s.1.1 i j ∈ Ov E w := by
    refine hK.eventually_forall_of_forall_eventually fun s _ => ?_
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) := by fun_prop
    have h0 : (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) (0, s) ∈ (Ov E w : Set _) := by
      simp only [zero_mul]; exact (Ov E w).zero_mem
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set (w.adicCompletion E))))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (w.adicCompletion E))))).exists
  exact ⟨a, ha0, fun k i j => ha _ (subset_closure ⟨k, rfl⟩) i j⟩

end GlobalTheory.BddCpt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  first | exact @GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | exact GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZero

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceGram

theorem det_trace_pow_gram_ne_zero {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : g.charpoly.Separable) :
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  set M : Matrix (Fin n) (Fin n) L := g.map f
  have hMc : M.charpoly = g.charpoly.map f := Matrix.charpoly_map g f
  have hnd : M.charpoly.roots.Nodup := by
    rw [hMc]; exact nodup_roots (hg.map)
  have hcard : M.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]
  set s := M.charpoly.roots.toFinset
  let e : Fin n ≃ s := (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm
  let v : Fin n → L := fun i => (e i : L)
  have hv : Function.Injective v := fun a b h => e.injective (Subtype.ext h)
  have hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i) := by
    intro φ
    have : M.charpoly.roots = s.val := by
      simp [s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m := by
    intro m
    have h1 : f (g ^ m).trace = (M ^ m).trace := by
      have hp : M ^ m = (g ^ m).map f := by simp [M, Matrix.map_pow]

      rw [hp]; simp [Matrix.trace, Matrix.map_apply, map_sum]
    rw [h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]
  have hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f
      = (vandermonde v)ᵀ * vandermonde v := by
    ext i j
    rw [vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]
  intro h0
  have hd := RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)
  rw [h0, map_zero] at hd
  have h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0 := by
    rw [← hG]; exact hd.symm
  rw [det_mul, det_transpose, mul_self_eq_zero] at h2
  exact det_vandermonde_ne_zero_iff.mpr hv h2

end GlobalTheory.TraceGram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  first | exact @GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | exact GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | (intros; apply GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommute

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepCommutant

theorem exists_eq_sum_pow_of_commute :
    ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  intro K _ n g t hs hc
  have hm := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute g t hs hc
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, rfl⟩ := hm
  set r := p %ₘ g.charpoly with hr
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hae : aeval g p = aeval g r := by
    exact (Polynomial.aeval_modByMonic_eq_self_of_root (Matrix.aeval_self_charpoly g)).symm
  have hdeg : r.degree < n := by
    have := Polynomial.degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  refine ⟨fun i => r.coeff i, ?_⟩
  change aeval g p = _
  rw [hae, aeval_def, eval₂_eq_sum, ← Polynomial.sum_fin (fun e a => algebraMap K (Matrix (Fin n) (Fin n) K) a * g ^ e) (by simp) hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]

end GlobalTheory.SepCommutant
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommuteStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  first | exact @GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | exact GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | (intros; apply GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAll

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodCpt

theorem pow_mem_of_mem {K : Type} [Field K] (O : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) : ∀ k : ℕ, ∀ i j, (M ^ k) i j ∈ O := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun m _ => O.mul_mem (ih i m) (hM m j)

theorem gram_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin n => ((g.map f) ^ ((i : ℕ) + j)).trace) =
      (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f := by
  ext i j

  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← Matrix.map_pow, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  intro E _ _ _ hU n γ hs
  set g : Matrix (Fin n) (Fin n) E := γ.1.val with hgdef
  set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hd : G.det ≠ 0 := GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable g hs
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E (g i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.LocRatPt.eventually_valuation_le_one _
  filter_upwards [h1, GlobalTheory.LocRatPt.eventually_valuation_le_one (E := E) G.det⁻¹] with w hg hdi
  set f : E →+* w.adicCompletion E := algebraMap E (w.adicCompletion E)
  set gw : Matrix (Fin n) (Fin n) (w.adicCompletion E) := g.map f with hgw
  have hgwO : ∀ i j, gw i j ∈ Ov E w := fun i j => GlobalTheory.LocRatPt.algebraMap_mem_Ov (hg i j)
  have hsep : gw.charpoly.Separable := by rw [hgw, Matrix.charpoly_map]; exact hs.map
  have hGw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace) = G.map f := gram_map f g
  have hdet : (G.map f).det = f G.det := (RingHom.map_det f G).symm
  have hdw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
    rw [hGw, hdet]; exact (map_ne_zero f).2 hd
  have hdwi : ((Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ Ov E w := by
    rw [hGw, hdet, ← map_inv₀]; exact GlobalTheory.LocRatPt.algebraMap_mem_Ov hdi
  have hloc : (locPt w γ).1.1 = gw := by rw [GlobalTheory.LocRatPt.locPt_val hU]; rfl
  have key : ∀ s : UL n w, s * locPt w γ = locPt w γ * s →
      (∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (s ^ k).1.1 i j ∈ Ov E w) →
      ∀ i j, s.1.1 i j ∈ Ov E w := by
    rintro s hs' ⟨a, ha, hb⟩
    set x : Matrix (Fin n) (Fin n) (w.adicCompletion E) := s.1.1 with hx
    have hxc : x * gw = gw * x := by
      have := congrArg (fun u : UL n w => u.1.1) hs'
      simpa [hloc] using this
    have hpow : ∀ k : ℕ, (s ^ (k : ℤ)).1.1 = x ^ k := by
      intro k; rw [zpow_natCast]; simp [hx]
    obtain ⟨c, hcx⟩ := GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable gw x hsep hxc
    refine GlobalTheory.T.entry_mem_subring_of_trace_gram_unit (Ov E w) gw x c hcx hgwO (fun j => ?_) hdw hdwi
    refine GlobalTheory.T.trace_mem_of_mul_pow_entries_mem E w n _ a ha fun k i l => ?_
    have hcm : Commute x (gw ^ (j : ℕ)) := (Commute.pow_right hxc (j : ℕ))
    rw [hcm.mul_pow, ← pow_mul, Matrix.mul_apply, Finset.mul_sum]
    refine (Ov E w).sum_mem fun m _ => ?_
    rw [← mul_assoc, ← hpow]
    exact (Ov E w).mul_mem (hb _ i m) (pow_mem_of_mem _ gw hgwO _ m l)
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  have ht' : t * locPt w γ = locPt w γ * t := ht
  obtain ⟨a, ha, hb⟩ := GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary E n w t hc
  have e1 := key t ht' ⟨a, ha, hb⟩
  have e2 := key t⁻¹ ((show Commute t (locPt w γ) from ht').inv_left).eq
    ⟨a, ha, fun k i j => by rw [_root_.inv_zpow']; exact hb (-k) i j⟩
  rw [SetLike.mem_coe, KL, Subgroup.mem_subgroupOf]
  exact GlobalTheory.LocRatPt.mem_GLint_of_entries e1 (fun i j => by simpa using e2 i j)

end GlobalTheory.BCT.GoodCpt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAllStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.centraliser_compactPart_le_integral_almostAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  first | exact @GlobalTheory.BCT.GoodCpt.main | exact GlobalTheory.BCT.GoodCpt.main | (intros; apply GlobalTheory.BCT.GoodCpt.main <;> assumption)
end
end
