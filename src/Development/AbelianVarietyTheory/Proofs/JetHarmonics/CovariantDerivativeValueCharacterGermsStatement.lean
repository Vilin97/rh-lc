module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGroupedOfSublist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThirdPointDerivativeAtZeroSeriesMemIntegral

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDmonOfEigen

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CharacterColumns

theorem dof_zero_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (f : PS R 1 d) :
    Dof F 0 f = 0 := by
  simp [Dof]

theorem dmonOf_congr_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u u' : ι → Fin d → R) (mo : ι →₀ ℕ) (hu : ∀ l, mo l ≠ 0 → u l = u' l)
    (f : PS R 1 d) : DmonOf F u mo f = DmonOf F u' mo f := by
  unfold DmonOf
  congr 1
  funext l g
  by_cases hl : mo l = 0
  · rw [hl]; rfl
  · rw [hu l hl]

theorem nabVal_congr_dir {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (w0 : O)
    (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u u' : ι → Fin d → k) (mo : ι →₀ ℕ)
    (hu : ∀ l, mo l ≠ 0 → u l = u' l) :
    B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) =
      B.nabVal k h w0 m f u' (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one,
    dmonOf_congr_dir _ u u' mo hu]

theorem constantCoeff_dmonOf_eigen {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (S : Set ι) (χ : PS R 1 d) (y : ι → R)
    (h1 : constantCoeff χ = 1) (hχ : ∀ l ∈ S, Dof F (u l) χ = C (y l) * χ) (mo : ι →₀ ℕ)
    (hmo : ∀ l, mo l ≠ 0 → l ∈ S) :
    constantCoeff (DmonOf F (S.indicator u) mo χ) = ∏ l, y l ^ mo l := by
  have key := constantCoeff_dmonOf_sub_mem R d F ⊥ ι (S.indicator u) (S.indicator y) χ (by
    intro l mo'
    by_cases hl : l ∈ S
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, hχ l hl, sub_self, map_zero]
      exact Ideal.zero_mem _
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, dof_zero_dir, map_zero, zero_mul,
        sub_self, map_zero]
      exact Ideal.zero_mem _) mo
  rw [Ideal.mem_bot, sub_eq_zero, h1, mul_one] at key
  rw [key]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : mo l = 0
  · rw [hl, pow_zero, pow_zero]
  · rw [Set.indicator_of_mem (hmo l hl)]

end GlobalTheory.CharacterColumns

namespace GlobalTheory

open CharacterColumns

theorem nabVal_character_columns :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  intro COL R _ d O _ _ k _ _ _ B h hh hinj w0 N m n I hN a c hac ι _ u S α hα hβ χ y h1 hχ P hP
  classical
  have hcol : ∀ b, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, (∀ l, mo l ≠ 0 → l ∈ S b) → ∃ s : R,
      s - ∏ l, y (l, b) ^ mo l ∈ I ∧
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
    intro b
    have hz : (fun i => algebraMap R k ((0 : Fin d → R) i)) = 0 := by
      funext i; simp
    obtain ⟨g, hg⟩ := COL R d O k B h hh hinj w0 (a b) (c b) N m I (hac b) hN ι ((S b).indicator u)
      (fun l => if l ∈ S b then α b l else 1)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).1
        · rw [if_neg hl, sub_self]; exact I.zero_mem)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).2.1
        · rw [if_neg hl]; exact isUnit_one)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl, Set.indicator_of_mem hl]; exact (hα b l hl).2.2
        · rw [Set.indicator_of_notMem hl, hz, Matrix.mulVec_zero, smul_zero])
      (by
        intro l l'
        by_cases hl : l ∈ S b
        · by_cases hl' : l' ∈ S b
          · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl']; exact hβ b l hl l' hl'
          · rw [Set.indicator_of_notMem hl', hz, Matrix.mulVec_zero, Matrix.mulVec_zero,
              dotProduct_zero]
            exact zero_mem _
        · rw [Set.indicator_of_notMem hl, hz, zero_dotProduct]
          exact zero_mem _)
      (χ b)
    refine ⟨g, fun mo hmo => ?_⟩
    obtain ⟨r, hr, e⟩ := hg mo
    refine ⟨∏ l, y (l, b) ^ mo l + r, by rwa [add_sub_cancel_left], ?_⟩
    rw [constantCoeff_dmonOf_eigen B.G.F u (S b) (χ b) (fun l => y (l, b)) (h1 b) (hχ b) mo hmo] at e
    rw [← e]
    refine nabVal_congr_dir B h w0 m _ _ _ mo fun l hl => ?_
    rw [Set.indicator_of_mem (hmo l hl)]
  choose g hg using hcol
  have hs : ∀ (mo : ι × Fin n →₀ ℕ) (b : Fin n), ∃ s : R, mo ∈ P.support →
      s - ∏ l, y (l, b) ^ mo (l, b) ∈ I ∧
      B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k s := by
    intro mo b
    by_cases hmo : mo ∈ P.support
    · obtain ⟨s, hs⟩ := hg b (colM mo b) (fun l hl => hP mo hmo l b hl)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h' => absurd h' hmo⟩
  choose s hs using hs
  refine ⟨g, ∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b - MvPolynomial.eval y P, ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo hmo => ?_
    rw [← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b hmo).1
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [add_sub_cancel, map_sum]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => (hs mo b hmo).2

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DmonOfMulCongrOfCongr

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem dmonOf_mul_congr_of_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) := by
  intro R _ d F I ι _ u f f' g h mo
  have hsub : ∀ (m : ι →₀ ℕ) (a b : PS R 1 d),
      DmonOf F u m (a - b) = DmonOf F u m a - DmonOf F u m b := fun m a b => by
    have e := ExpCong.along_add (fun l => Dof F (u l)) (fun l => GE.dof_add F (u l))
      (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (a - b) b
    rw [sub_add_cancel, ← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along,
      ← ExpCong.dmonOf_eq_along] at e
    rw [e, add_sub_cancel_right]
  have key := ExpCong.along_mul_mem (fun l => Dof F (u l)) (constantCoeff : PS R 1 d →+* R)
    (fun a => GE.dof_add F (u a)) (fun a => GE.dof_mul F (u a)) Set.univ I.toAddSubgroup
    (fun s _ j hj => I.mul_mem_left s hj)
    (ExpCong.grouped (Finset.univ : Finset ι).toList mo).reverse g (f - f')
    (fun _ _ => Set.mem_univ _)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F u mo v hv
      rw [hm', hsub, map_sub]
      exact h m')
  rw [← ExpCong.dmonOf_eq_along, show g * (f - f') = f * g - f' * g by ring, hsub, map_sub] at key
  exact key

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralGermNabValCongr

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.IntegralColumnGerm

theorem prod_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) {ι : Type} [Fintype ι] (α : ι → R)
    (hα : ∀ l, α l - 1 ∈ I) (n : ι → ℕ) : ∏ l, α l ^ n l - 1 ∈ I := by
  rw [← Ideal.Quotient.eq, map_prod, map_one]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [map_pow, Ideal.Quotient.eq.2 (hα l), map_one, one_pow]

theorem exists_eq_of_unit_mul {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) (I : Ideal R) {P x y : R}
    {v : k} (hP : IsUnit P) (hP1 : P - 1 ∈ I) (hxy : x - y ∈ I) (h : φ P * v = φ x) :
    ∃ r ∈ I, v = φ (y + r) := by
  obtain ⟨Q, hQ⟩ := hP.exists_left_inv
  refine ⟨Q * ((x - y) - (P - 1) * y), I.mul_mem_left _ (I.sub_mem hxy (I.mul_mem_right _ hP1)), ?_⟩
  have e : y + Q * ((x - y) - (P - 1) * y) = Q * x := by linear_combination (-y) * hQ
  rw [e, map_mul, ← h, ← mul_assoc, ← map_mul, hQ, map_one, one_mul]

end GlobalTheory.IntegralColumnGerm

namespace GlobalTheory

open IntegralColumnGerm

theorem exists_integral_germ_nabVal_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by
  intro hS hL R _ d O _ _ k _ _ _ B h hh hinj w0 a c N m I hac hN ι _ u α hα1 hαu hα hβ χ
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : ∀ w : O, constantCoeff (B.hL k h w) = 0 := fun w =>
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w) (gp_pt 0))) h hh0
  have e0 : star a * (w0 * a) = (N : O) * (c * w0) := by linear_combination w0 * hac
  have h1 := FramePull.expIntegral_ad hh a 1 (w0 * a)
  rw [e0, mul_one, ← FramePull.ev_actK_hL, ← FramePull.hL_eq] at h1
  obtain ⟨cD, υ, υ1, hυ⟩ := h1
  have hinv : υ * invOfUnit υ 1 = 1 := mul_invOfUnit υ 1 (by simpa using υ1)
  obtain ⟨g, hg⟩ : ∃ g : PS R 1 d, g * υ ^ m = χ :=
    ⟨χ * invOfUnit υ 1 ^ m, by rw [mul_assoc, ← mul_pow, mul_comm _ υ, hinv, one_pow, mul_one]⟩
  refine ⟨g, fun mo => ?_⟩
  have hga : FB.toK k (ev (n := 1) ![B.A.act a] g) = ev (n := 1) ![B.actK k a] (FB.toK k g) := by
    rw [FB.toK, QuadDeriv.map_ev _ _ (single_point_zero_constant (B.A.const a))]
    congr 1
    funext j; fin_cases j; rfl
  have hG : ev (n := 1) ![B.actK k a] (FB.toK k g * FB.expS k ((m : k) • B.hL k h w0)) =
      FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) *
        FB.expS k ((m : k) • B.hL k h ((N : O) * (c * w0))) := by
    have e : FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) =
        FB.toK k (ev (n := 1) ![B.A.act a] g) * FB.toK k υ ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hga, hυ, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, sub_add_cancel]
  have hend := (invariantDeriv_along_endo R d O k B a).2 ι (fun l i => algebraMap R k (u l i))
    (fun l => algebraMap R k (α l)) hα
  have hmap : ∀ (mo : ι →₀ ℕ) (f : PS R 1 d),
      constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (FB.toK k f)) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo f)) := fun mo f => by
    rw [← constantCoeff_map, map_dmonOf]
    rfl
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • B.hL k h ((N : O) * (c * w0)))) = algebraMap R k r := by
    intro mo
    obtain ⟨t, ht⟩ := hS R d O k B h hh (c * w0) N ι u hβ mo
    refine ⟨(m : R) * (N * t), I.mul_mem_left _ (I.mul_mem_right _ hN), ?_⟩
    rw [smul_eq_C_mul, GE.dmonOf_Cmul, map_mul, constantCoeff_C, ht, map_mul (algebraMap R k) (m : R),
      map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cL, mul_zero]) hφ (ev (n := 1) ![B.A.act a] g * υ ^ m) mo
  have hcong : ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) -
      constantCoeff (DmonOf B.G.F u mo g) ∈ I := by
    intro mo
    have e1 : constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) =
        (∏ l, α l ^ mo l) * constantCoeff (DmonOf B.G.F u mo g) := by
      apply hinj
      rw [← hmap, hga, hend, hmap]
      simp only [map_mul, map_prod, map_pow]
    rw [e1, ← sub_one_mul]
    exact I.mul_mem_right _ (prod_pow_sub_one_mem I α hα1 mo)
  have hleib := hL R d B.G.F I ι u _ _ (υ ^ m) hcong mo
  rw [hg] at hleib
  refine exists_eq_of_unit_mul (algebraMap R k) I (P := ∏ l, α l ^ mo l)
    (x := constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g * υ ^ m)) + r)
    (IsUnit.prod_univ_iff.2 fun l => (hαu l).pow _) (prod_pow_sub_one_mem I α hα1 mo) ?_ ?_
  · rw [add_sub_right_comm]
    exact I.add_mem hleib hr
  · unfold FB.nabVal
    rw [PullbackColumn.dpolyOf_monomial_one, ← e]
    simp only [map_prod, map_pow]
    rw [← hend, hG]
    rfl

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms

section

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem nabVal_character_columns_of_canonGauge : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) :=
  GlobalTheory.nabVal_character_columns (GlobalTheory.exists_integral_germ_nabVal_congr
    GlobalTheory.canonGauge_dmonOf_hL_natCast_mul GlobalTheory.dmonOf_mul_congr_of_congr)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGermsStatement

section

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

theorem _root_.GlobalTheory.T.covariantDerivative_value_character_germs : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  first | exact @GlobalTheory.nabVal_character_columns_of_canonGauge | exact GlobalTheory.nabVal_character_columns_of_canonGauge | (intros; apply GlobalTheory.nabVal_character_columns_of_canonGauge <;> assumption)
end
end
