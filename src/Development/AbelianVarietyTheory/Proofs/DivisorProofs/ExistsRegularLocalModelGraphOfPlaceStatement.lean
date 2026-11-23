module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrdStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiserStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrimeStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem exists_isUnit_mul_zpow_tmul :
    ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  intro K κ' L _ _ _ _ _ _ E 𝔭 _ t _ ht g hg
  set n := E.ord g
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set u : K := g * (t : K) ^ (-n) with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hg (zpow_ne_zero _ ht0)
  have hord : E.ord u = 0 := by
    rw [hu_def, E.ord_mul hg (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  have hu : u ∈ E.ring := (E.ord_nonneg_iff hu0).1 hord.ge
  have hui : u⁻¹ ∈ E.ring := (E.ord_nonneg_iff (inv_ne_zero hu0)).1 (by rw [E.ord_inv, hord]; simp)
  let b : tens (κ' := κ') (placeAlg E) := ⟨u ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hu) 1⟩
  let b' : tens (κ' := κ') (placeAlg E) := ⟨u⁻¹ ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hui) 1⟩
  have hbb : b * b' = 1 := by
    apply Subtype.ext
    change (u ⊗ₜ[ℂ] (1 : κ')) * (u⁻¹ ⊗ₜ 1) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hu0, one_mul]
    rfl
  refine ⟨toQ (L := L) 𝔭 b, (IsUnit.of_mul_eq_one (b := b') hbb).map _, ?_⟩
  let φ : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hφ (x : K) : φ x = algebraMap (K ⊗[ℂ] κ') L (x ⊗ₜ 1) := rfl
  have hg' : g = u * (t : K) ^ n := by
    rw [hu_def, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  rw [coe_toQ, ← hφ, ← hφ, ← hφ, ← map_zpow₀, ← map_mul, ← hg']

end GlobalTheory.GraphLocal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmulStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  first | exact @GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | exact GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | (intros; apply GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

theorem sum_notMem_of_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ hle hR l a b w hw hc
  let g : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨(a i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (a i)),
      sub_mem (tmul_mem (hR _ (a i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩
  let bb : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨1 ⊗ₜ b i, tmul_mem (one_mem (placeAlg E)) _⟩
  let u : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i), tmul_mem (one_mem (placeAlg E)) _⟩
  let v : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i)⁻¹, tmul_mem (one_mem (placeAlg E)) _⟩
  have hg : ∀ i, g i ∈ graphIdeal E R π ρ := fun i => Ideal.subset_span (Or.inr ⟨a i, rfl⟩)
  have hsum : w - u = ∑ i, g i * bb i := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, hw, AddSubmonoidClass.coe_finsetSum]
    simp only [g, bb, u, Subalgebra.coe_mul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Finset.sum_sub_distrib, TensorProduct.tmul_sum]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp only [u, v, Subalgebra.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hc, Subalgebra.coe_one, Algebra.TensorProduct.one_def]
  have hu : u ∉ 𝔭 := fun h => one_notMem 𝔭 (huv ▸ 𝔭.mul_mem_right v h)
  intro hwp
  have hd : w - u ∈ 𝔭 :=
    hle (hsum ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hg i))
  exact hu (by simpa using 𝔭.sub_mem hwp hd)

end GlobalTheory.GraphLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  first | exact @GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | exact GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | (intros; apply GlobalTheory.GraphLocal.sum_notMem_of_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

theorem GlobalTheory.GraphLocal.exists_locModel_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO' hz hcompat hC hfrac E hER hcentre
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes (GlobalTheory.T.placeGraphIdealTensor_ne_top (κ' := κ') R π ρ E hcompat hC hfrac hER hcentre)
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have hle : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
  have hQ : IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor E 𝔭 hO'
  letI := hQ.isLocalRing
  have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hcompat hC hfrac hcentre ht hzR h𝔭
  have hdim := GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime (L := L) k R π ρ E 𝔭 hO' hcompat hC hfrac hER hcentre hz h𝔭
  have hz0 : ((toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0) : locAt (L := L) 𝔭) : L) =
      algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1) := by
    simp [gens]
  refine ⟨locAt (L := L) 𝔭, hQ, fun i => toQ 𝔭 (gens E R π ρ hER t zR i), hmax, hdim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (toQ (L := L) 𝔭 ⟨e ⊗ₜ 1, tmul_mem (A := placeAlg E) he 1⟩).2
  · intro g hg
    rw [hz0]
    exact GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul E 𝔭 t hinj ht g hg
  · intro b hb
    refine ⟨toQ 𝔭 ⟨1 ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩, isUnit_toQ 𝔭 hinj ?_, rfl⟩
    intro h
    apply one_notMem 𝔭
    have h2 := 𝔭.mul_mem_right ⟨(1 : K) ⊗ₜ b⁻¹, tmul_mem (one_mem (placeAlg E)) b⁻¹⟩ h
    convert h2 using 1
    apply Subtype.ext
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hb, Algebra.TensorProduct.one_def]
  · intro l a b hs
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, isUnit_toQ 𝔭 hinj (GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero R π ρ E 𝔭 hle hER l a b ⟨_, hw⟩ rfl hs), ?_⟩

    simp [map_sum]
  · intro M l a b hJ
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, by simp [map_sum], ?_⟩
    have h1 := GlobalTheory.T.graphJets_mem_pow_sup_uniformiser R π ρ E 𝔭 t hle ht hcompat hC hfrac hER hcentre M l a b ⟨_, hw⟩ rfl hJ
    have h2 := Ideal.mem_map_of_mem (toQ (L := L) 𝔭) h1
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
    have h3 : Ideal.map (toQ (L := L) 𝔭) 𝔭 ^ M ⊔ Ideal.span {toQ (L := L) 𝔭 ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} ≤
        IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ^ M ⊔
          Ideal.span {toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0)} :=
      sup_le_sup (Ideal.pow_right_mono (map_le_maximalIdeal 𝔭 hinj) M) le_rfl
    exact h3 h2
  · obtain ⟨y, q, hy, hq, e⟩ := GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order n k' x τ' E 𝔭 t hQ.const_mem hx hτ hO' ht
    refine ⟨y, q, hy, hq, ?_⟩
    rw [hz0]
    exact e
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_regular_localModel_graph_of_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_locModel_graph | exact GlobalTheory.GraphLocal.exists_locModel_graph | (intros; apply GlobalTheory.GraphLocal.exists_locModel_graph <;> assumption)
end
end
